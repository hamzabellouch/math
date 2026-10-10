import OAI.Combinatorics.BalancedRyser.Incidence.CandidateConditionalFreshIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.CandidatePartialPointIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.PartialIncidenceCounts
import OAI.Combinatorics.BalancedRyser.Probability.FullyExposedTargets
import OAI.Combinatorics.BalancedRyser.Probability.RootSuccess

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def admissibleCodes (D : Finset (Direction F)) (j : ℕ) : Finset (IncidenceCode F) :=
  ((tupleCodesWithOldCount D j).product Finset.univ).filter
    (fun z => Function.Injective z.1.1 ∧ ∀ i, z.1.1 i ≠ z.2)

def probability (D : Finset (Direction F)) (a : MergedPairs F)
    (E : Set (MergedPairs F)) : ℝ :=
  (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (canonical_exposure_supported D a)).toOuterMeasure E).toReal

def codeEvent (P : Direction F → (Fin 4 → Point F) → Prop)
    (z : IncidenceCode F) : Set (MergedPairs F) :=
  {M | SuccessfulPositions (tuplePoint M ⟨z.1.1,z.1.2⟩) z.2 ∧
    P z.2 (tuplePoint M ⟨z.1.1,z.1.2⟩)}

def incidenceSum (D : Finset (Direction F)) (a : MergedPairs F) (j : ℕ)
    (P : Direction F → (Fin 4 → Point F) → Prop) : ℝ :=
  ∑ z ∈ admissibleCodes D j, probability D a (codeEvent P z)

theorem probability_mono (D : Finset (Direction F)) (a : MergedPairs F)
    {E G : Set (MergedPairs F)} (h : E ⊆ G) :
    probability D a E ≤ probability D a G := by
  unfold probability
  apply ENNReal.toReal_mono _ (MeasureTheory.measure_mono h)
  have hu : ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure Set.univ = 1 := by
    exact (PMF.toOuterMeasure_apply_eq_one_iff _ Set.univ).mpr (Set.subset_univ _)
  exact ne_of_lt ((MeasureTheory.measure_mono (Set.subset_univ G)).trans_lt
    (by rw [hu]; exact ENNReal.one_lt_top))

omit [Field F] in
theorem mem_admissibleCodes {D : Finset (Direction F)} {j : ℕ}
    {z : IncidenceCode F} (hz : z ∈ admissibleCodes D j) :
    Function.Injective z.1.1 ∧ (∀ i, z.1.1 i ≠ z.2) ∧
      (exposedTupleIndices (⟨z.1.1,z.1.2⟩ : FourTuple F) D).card = j := by
  obtain ⟨hcode,hinj,hg⟩ := Finset.mem_filter.mp hz
  refine ⟨hinj,hg,?_⟩
  have h := (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp hcode).1).1).2
  exact h

omit [Field F] in
theorem generators_fresh_of_mem_zero {D : Finset (Direction F)}
    {z : IncidenceCode F} (hz : z ∈ admissibleCodes D 0) :
    ∀ i, z.1.1 i ∉ D := by
  have hzero := Finset.card_eq_zero.mp (mem_admissibleCodes hz).2.2
  intro i hi
  have hmem : i ∈ exposedTupleIndices (⟨z.1.1,z.1.2⟩ : FourTuple F) D := by
    simpa [exposedTupleIndices] using hi
  rw [hzero] at hmem
  exact Finset.notMem_empty i hmem

omit [Field F] in
theorem card_admissibleCodes_le (D : Finset (Direction F)) (j : ℕ) :
    (admissibleCodes D j).card ≤
      (16 * (Nat.choose 4 j * D.card ^ j *
        Fintype.card (Direction F) ^ (4-j))) * Fintype.card (Direction F) := by
  calc
    _ ≤ ((tupleCodesWithOldCount D j).product
        (Finset.univ : Finset (Direction F))).card := Finset.card_filter_le _ _
    _ = (tupleCodesWithOldCount D j).card * Fintype.card (Direction F) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_tupleCodesWithOldCount_le D j)

omit [DecidableEq F] in
private theorem card_direction_le_twice :
    (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have h : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    simp only [Direction, Fintype.card_option]
    omega
  exact_mod_cast h

theorem sum_zero_le (D : Finset (Direction F)) (f : IncidenceCode F → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ z ∈ admissibleCodes D 0, f z ≤ A * (Fintype.card F : ℝ)⁻¹^5) :
    (∑ z ∈ admissibleCodes D 0, f z) ≤ 512 * A := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((admissibleCodes D 0).card : ℝ) ≤
      16 * (Fintype.card (Direction F) : ℝ)^5 := by
    have hn : (admissibleCodes D 0).card ≤ 16 * Fintype.card (Direction F)^5 := by
      calc
        _ ≤ _ := card_admissibleCodes_le D 0
        _ = _ := by norm_num only [Nat.choose_zero_right, pow_zero, Nat.sub_zero]; ring
    exact_mod_cast hn
  calc
    _ ≤ ∑ _z ∈ admissibleCodes D 0, A * (Fintype.card F : ℝ)⁻¹^5 :=
      Finset.sum_le_sum hf
    _ = ((admissibleCodes D 0).card : ℝ) * (A * (Fintype.card F : ℝ)⁻¹^5) := by simp
    _ ≤ (16 * (Fintype.card (Direction F) : ℝ)^5) *
        (A * (Fintype.card F : ℝ)⁻¹^5) := by gcongr
    _ ≤ (16 * (2 * (Fintype.card F : ℝ))^5) *
        (A * (Fintype.card F : ℝ)⁻¹^5) := by
      gcongr
      exact card_direction_le_twice
    _ = _ := by field_simp; ring

theorem sum_one_le (D : Finset (Direction F)) (f : IncidenceCode F → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ z ∈ admissibleCodes D 1, f z ≤ A * (Fintype.card F : ℝ)⁻¹^4) :
    (∑ z ∈ admissibleCodes D 1, f z) ≤ 1024 * A * (D.card : ℝ) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((admissibleCodes D 1).card : ℝ) ≤
      64 * (D.card : ℝ) * (Fintype.card (Direction F) : ℝ)^4 := by
    have hn : (admissibleCodes D 1).card ≤
        64 * D.card * Fintype.card (Direction F)^4 := by
      calc
        _ ≤ _ := card_admissibleCodes_le D 1
        _ = _ := by norm_num only [Nat.choose_one_right, pow_one, Nat.reduceSub]; ring
    exact_mod_cast hn
  calc
    _ ≤ ∑ _z ∈ admissibleCodes D 1, A * (Fintype.card F : ℝ)⁻¹^4 :=
      Finset.sum_le_sum hf
    _ = ((admissibleCodes D 1).card : ℝ) * (A * (Fintype.card F : ℝ)⁻¹^4) := by simp
    _ ≤ (64 * (D.card : ℝ) * (Fintype.card (Direction F) : ℝ)^4) *
        (A * (Fintype.card F : ℝ)⁻¹^4) := by gcongr
    _ ≤ (64 * (D.card : ℝ) * (2 * (Fintype.card F : ℝ))^4) *
        (A * (Fintype.card F : ℝ)⁻¹^4) := by
      gcongr
      exact card_direction_le_twice
    _ = _ := by field_simp; ring

theorem code_probability_le_alignment (D : Finset (Direction F)) (a : MergedPairs F)
    (P : Direction F → (Fin 4 → Point F) → Prop) (z : IncidenceCode F) :
    probability D a (codeEvent P z) ≤ probability D a
      {M | (∃ c, ∀ i, OnLine (tuplePoint M ⟨z.1.1,z.1.2⟩ i) (z.2,c)) ∧
        P z.2 (tuplePoint M ⟨z.1.1,z.1.2⟩)} := by
  exact probability_mono D a (fun _ h => ⟨h.1.1,h.2⟩)

def designatesPoint (y : Point F) : Direction F → (Fin 4 → Point F) → Prop :=
  fun _ p => ∃ i, p i = y

def throughPointHitsLine (y : Point F) (K : Line F) :
    Direction F → (Fin 4 → Point F) → Prop :=
  fun g p => (∀ i, OnLine (p i) (lineThrough g y)) ∧ ∃ i, OnLine (p i) K

def hitsTwoLines (L K : Line F) : Direction F → (Fin 4 → Point F) → Prop :=
  fun _ p => ∃ i j : Fin 4, i ≠ j ∧ OnLine (p i) L ∧ OnLine (p j) K

theorem point_sum_zero_le (D : Finset (Direction F)) (a : MergedPairs F)
    (y : Point F) : incidenceSum D a 0 (designatesPoint y) ≤ 2048 := by
  change (∑ z ∈ admissibleCodes D 0, _) ≤ _
  refine (sum_zero_le D (fun z => probability D a (codeEvent (designatesPoint y) z))
    4 (by norm_num) ?_).trans (by norm_num)
  intro z hz
  have hb := CandidateFreshIncidence.conditional_tuple_contains_point_probability_le
    (⟨z.1.1,z.1.2⟩ : FourTuple F) (mem_admissibleCodes hz).1 D a
    (generators_fresh_of_mem_zero hz) z.2 y
  exact (code_probability_le_alignment D a _ z).trans hb

theorem point_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (y : Point F) : incidenceSum D a 1 (designatesPoint y) ≤ 1024 * (D.card : ℝ) := by
  change (∑ z ∈ admissibleCodes D 1, _) ≤ _
  refine (sum_one_le D (fun z => probability D a (codeEvent (designatesPoint y) z))
    1 (by norm_num) ?_).trans (by norm_num)
  intro z hz
  have hz' := mem_admissibleCodes hz
  have hb := CandidatePartialPointIncidence.conditional_tuple_contains_point_probability_le
    (⟨z.1.1,z.1.2⟩ : FourTuple F) hz'.1 D a (by omega) z.2 hz'.2.1 y
  simpa only [one_mul] using
    (code_probability_le_alignment D a _ z).trans hb

theorem point_line_sum_zero_le (D : Finset (Direction F)) (a : MergedPairs F)
    (y : Point F) (K : Line F) (hyK : ¬ OnLine y K) :
    incidenceSum D a 0 (throughPointHitsLine y K) ≤ 2048 := by
  change (∑ z ∈ admissibleCodes D 0, _) ≤ _
  refine (sum_zero_le D
    (fun z => probability D a (codeEvent (throughPointHitsLine y K) z))
    4 (by norm_num) ?_).trans (by norm_num)
  intro z hz
  have hb := CandidateFreshIncidence.conditional_tuple_through_point_hits_line_probability_le
    (⟨z.1.1,z.1.2⟩ : FourTuple F) (mem_admissibleCodes hz).1 D a
    (generators_fresh_of_mem_zero hz) z.2 y K hyK
  exact (probability_mono D a (fun _ h => h.2)).trans hb

theorem point_line_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (y : Point F) (K : Line F) :
    incidenceSum D a 1 (throughPointHitsLine y K) ≤ 1024 * (D.card : ℝ) := by
  change (∑ z ∈ admissibleCodes D 1, _) ≤ _
  refine (sum_one_le D
    (fun z => probability D a (codeEvent (throughPointHitsLine y K) z))
    1 (by norm_num) ?_).trans (by norm_num)
  intro z hz
  have hz' := mem_admissibleCodes hz
  have hb := CandidatePartialPointIncidence.conditional_tuple_through_point_hits_line_probability_le
    (⟨z.1.1,z.1.2⟩ : FourTuple F) hz'.1 D a (by omega) z.2 hz'.2.1 y K
  simpa only [one_mul] using (probability_mono D a (fun _ h => h.2)).trans hb

theorem two_lines_sum_zero_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (hLK : L ≠ K) :
    incidenceSum D a 0 (hitsTwoLines L K) ≤ 6144 := by
  change (∑ z ∈ admissibleCodes D 0, _) ≤ _
  refine (sum_zero_le D (fun z => probability D a (codeEvent (hitsTwoLines L K) z))
    12 (by norm_num) ?_).trans (by norm_num)
  intro z hz
  have hb := CandidateFreshIncidence.conditional_tuple_hits_two_lines_probability_le
    (⟨z.1.1,z.1.2⟩ : FourTuple F) (mem_admissibleCodes hz).1 D a
    (generators_fresh_of_mem_zero hz) z.2 L K hLK
  exact (code_probability_le_alignment D a _ z).trans hb

theorem two_lines_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    incidenceSum D a 1 (hitsTwoLines L K) ≤ 4096 * (D.card : ℝ) := by
  change (∑ z ∈ admissibleCodes D 1, _) ≤ _
  refine (sum_one_le D (fun z => probability D a (codeEvent (hitsTwoLines L K) z))
    4 (by norm_num) ?_).trans (by norm_num)
  intro z hz
  have hz' := mem_admissibleCodes hz
  have hb := CandidatePartialPointIncidence.conditional_tuple_hits_two_lines_probability_le
    (⟨z.1.1,z.1.2⟩ : FourTuple F) hz'.1 D a (by omega) z.2 hz'.2.1 L K havoid
  exact (code_probability_le_alignment D a _ z).trans hb

end
end Balanced.CandidateIncidenceSums

end OAI
