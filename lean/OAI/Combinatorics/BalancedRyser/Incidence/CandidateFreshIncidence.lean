import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.GlobalTupleLaw

namespace OAI

namespace Balanced.CandidateFreshIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def positionProbability (P : (Fin 4 → Point F) → Prop) : ℝ :=
  ((PMF.uniformOfFintype (Fin 4 → Point F)).toOuterMeasure {p | P p}).toReal

theorem offset_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (P : (Fin 4 → Point F) → Prop) :
    offsetEventProbability {M | P (tuplePoint M T)} = positionProbability P := by
  classical
  have h := congrArg (fun μ : PMF (Fin 4 → Point F) =>
    (μ.toOuterMeasure {p | P p}).toReal) (TupleAlignment.tuplePoint_uniform T hT)
  rw [PMF.toOuterMeasure_map_apply] at h
  exact h

omit [DecidableEq F] in
theorem positionProbability_eq_card (P : (Fin 4 → Point F) → Prop) :
    positionProbability P =
      (Fintype.card {p : Fin 4 → Point F // P p} : ℝ) / (Fintype.card F : ℝ)^8 := by
  classical
  rw [positionProbability, PMF.toOuterMeasure_uniformOfFintype_apply,
    ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_mul, Fintype.card_fun,
    Fintype.card_fin, Point, Fintype.card_prod, Nat.cast_pow, Nat.cast_mul]
  congr 1
  ring

omit [DecidableEq F] in
theorem positionProbability_mono {P Q : (Fin 4 → Point F) → Prop}
    (h : ∀ p, P p → Q p) : positionProbability P ≤ positionProbability Q := by
  classical
  rw [positionProbability_eq_card, positionProbability_eq_card]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Fintype.card_subtype_mono P Q h

omit [DecidableEq F] in
theorem positionProbability_exists_le {ι : Type*} [Fintype ι]
    (P : ι → (Fin 4 → Point F) → Prop) :
    positionProbability (fun p => ∃ i, P i p) ≤ ∑ i, positionProbability (P i) := by
  classical
  let : DecidablePred (fun p : Fin 4 → Point F => ∃ i, P i p) :=
    fun p => Classical.propDecidable (∃ i, P i p)
  simp_rw [positionProbability_eq_card]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : Fintype.card {p : Fin 4 → Point F // ∃ i, P i p} ≤
      Fintype.card (Σ i, {p : Fin 4 → Point F // P i p}) := by
    classical
    let f : {p : Fin 4 → Point F // ∃ i, P i p} →
        Σ i, {p : Fin 4 → Point F // P i p} := fun p =>
      ⟨Classical.choose p.2, p.1, Classical.choose_spec p.2⟩
    apply Fintype.card_le_of_injective f
    intro p r h
    apply Subtype.ext
    exact congrArg (fun z : Σ i, {p : Fin 4 → Point F // P i p} => z.2.1) h
  rw [Fintype.card_sigma] at hc
  exact_mod_cast hc

omit [DecidableEq F] in
theorem positionProbability_rectangle (S : Fin 4 → Finset (Point F)) :
    positionProbability (fun p => ∀ i, p i ∈ S i) =
      (∏ i, ((S i).card : ℝ)) / (Fintype.card F : ℝ)^8 := by
  classical
  let : DecidablePred (fun p : Fin 4 → Point F => ∀ i, p i ∈ S i) :=
    fun p => Classical.propDecidable (∀ i, p i ∈ S i)
  rw [positionProbability_eq_card]
  congr 1
  have hc : Fintype.card {p : Fin 4 → Point F // ∀ i, p i ∈ S i} =
      ∏ i, (S i).card := by
    classical
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun i x => x ∈ S i))]
    simp
  exact_mod_cast hc

theorem positionProbability_one_fixed (i : Fin 4) (y : Point F) (l : Line F) :
    positionProbability (fun p => ∀ j,
      p j ∈ if j = i then {y} else linePoints l) =
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  rw [positionProbability_rectangle]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  fin_cases i <;> simp [Fin.prod_univ_four, linePoints_card] <;>
    field_simp

theorem aligned_fixed_position_le (i : Fin 4) (y : Point F) (l : Line F) :
    positionProbability (fun p => (∀ j, OnLine (p j) l) ∧ p i = y) ≤
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  rw [← positionProbability_one_fixed i y l]
  apply positionProbability_mono
  intro p hp j
  by_cases hj : j = i
  · simp [hj, hp.2]
  · simp [hj, linePoints, hp.1 j]

theorem same_direction_fixed_position_le (g : Direction F) (i : Fin 4) (y : Point F) :
    positionProbability (fun p => (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ p i = y) ≤
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  apply (positionProbability_mono (Q := fun p =>
    (∀ j, OnLine (p j) (lineThrough g y)) ∧ p i = y) ?_).trans
      (aligned_fixed_position_le i y (lineThrough g y))
  rintro p ⟨⟨c, hc⟩, hi⟩
  refine ⟨?_, hi⟩
  intro j
  change lineEval g (p j) = lineEval g y
  exact (hc j).trans (by simpa [hi] using (hc i).symm)

theorem aligned_probability (l : Line F) :
    positionProbability (fun p => ∀ j, OnLine (p j) l) =
      (Fintype.card F : ℝ)⁻¹^4 := by
  classical
  have h := positionProbability_rectangle (fun _ : Fin 4 => linePoints l)
  simp only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] at h
  change positionProbability (fun p => ∀ j, OnLine (p j) l) =
    (∏ _i : Fin 4, ((linePoints l).card : ℝ)) / (Fintype.card F : ℝ)^8 at h
  rw [h, linePoints_card]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [DecidableEq F] in
theorem positionProbability_exists_le_card {ι : Type*} [Fintype ι]
    (P : ι → (Fin 4 → Point F) → Prop) (r : ℝ)
    (h : ∀ i, positionProbability (P i) ≤ r) :
    positionProbability (fun p => ∃ i, P i p) ≤ (Fintype.card ι : ℝ) * r := by
  classical
  calc
    _ ≤ ∑ i, positionProbability (P i) := positionProbability_exists_le P
    _ ≤ ∑ _i : ι, r := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

theorem same_direction_position_on_line_le (g : Direction F) (i : Fin 4) (l : Line F) :
    positionProbability (fun p =>
      (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ OnLine (p i) l) ≤
      (Fintype.card F : ℝ)⁻¹^4 := by
  classical
  by_cases hgl : g = l.1
  · rw [← aligned_probability l]
    apply positionProbability_mono
    rintro p ⟨⟨c, hc⟩, hi⟩ j
    have heq : (g,c) = l := eq_of_onLine_same_direction (p i) (g,c) l hgl (hc i) hi
    simpa only [heq] using hc j
  · let P : F → (Fin 4 → Point F) → Prop := fun c p =>
      (∀ j, OnLine (p j) (g,c)) ∧ p i = lineIntersection (g,c) l
    have hsub : ∀ p, ((∃ c, ∀ j, OnLine (p j) (g,c)) ∧ OnLine (p i) l) →
        ∃ c, P c p := by
      rintro p ⟨⟨c, hc⟩, hi⟩
      refine ⟨c, hc, ?_⟩
      exact common_point_eq_of_lines_ne (g,c) l
        (fun heq => hgl (congrArg Prod.fst heq)) (p i) (lineIntersection (g,c) l)
        (hc i) hi (onLine_lineIntersection_left _ _ hgl)
        (onLine_lineIntersection_right _ _ hgl)
    calc
      _ ≤ positionProbability (fun p => ∃ c, P c p) := positionProbability_mono hsub
      _ ≤ (Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹^5 :=
        positionProbability_exists_le_card P _
          (fun c => aligned_fixed_position_le i (lineIntersection (g,c) l) (g,c))
      _ = _ := by
        have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp

theorem same_direction_hits_line_le (g : Direction F) (l : Line F) :
    positionProbability (fun p =>
      (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, OnLine (p i) l) ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  classical
  let P : Fin 4 → (Fin 4 → Point F) → Prop := fun i p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ OnLine (p i) l
  apply (positionProbability_mono (Q := fun p => ∃ i, P i p) ?_).trans
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      positionProbability_exists_le_card P _ (fun i => same_direction_position_on_line_le g i l)
  · rintro p ⟨hc, i, hi⟩
    exact ⟨i, hc, hi⟩

theorem same_direction_contains_point_le (g : Direction F) (y : Point F) :
    positionProbability (fun p =>
      (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, p i = y) ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  let P : Fin 4 → (Fin 4 → Point F) → Prop := fun i p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ p i = y
  apply (positionProbability_mono (Q := fun p => ∃ i, P i p) ?_).trans
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      positionProbability_exists_le_card P _ (fun i => same_direction_fixed_position_le g i y)
  · rintro p ⟨hc, i, hi⟩
    exact ⟨i, hc, hi⟩

theorem aligned_position_on_other_line_le (i : Fin 4) (l k : Line F) (hlk : l ≠ k) :
    positionProbability (fun p => (∀ j, OnLine (p j) l) ∧ OnLine (p i) k) ≤
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  apply (positionProbability_mono (Q := fun p =>
    (∀ j, OnLine (p j) l) ∧ p i = lineIntersection l k) ?_).trans
      (aligned_fixed_position_le i (lineIntersection l k) l)
  rintro p ⟨hl, hk⟩
  refine ⟨hl, ?_⟩
  by_cases hd : l.1 = k.1
  · exact (hlk (eq_of_onLine_same_direction (p i) l k hd (hl i) hk)).elim
  · exact common_point_eq_of_lines_ne l k hlk (p i) (lineIntersection l k)
      (hl i) hk (onLine_lineIntersection_left _ _ hd)
      (onLine_lineIntersection_right _ _ hd)

theorem through_point_hits_line_le (g : Direction F) (y : Point F) (k : Line F)
    (hyk : ¬ OnLine y k) :
    positionProbability (fun p =>
      (∀ j, OnLine (p j) (lineThrough g y)) ∧ ∃ i, OnLine (p i) k) ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  have hlk : lineThrough g y ≠ k := by
    intro h
    exact hyk (h ▸ onLine_lineThrough g y)
  let P : Fin 4 → (Fin 4 → Point F) → Prop := fun i p =>
    (∀ j, OnLine (p j) (lineThrough g y)) ∧ OnLine (p i) k
  apply (positionProbability_mono (Q := fun p => ∃ i, P i p) ?_).trans
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      positionProbability_exists_le_card P _
        (fun i => aligned_position_on_other_line_le i (lineThrough g y) k hlk)
  · rintro p ⟨hc, i, hi⟩
    exact ⟨i, hc, hi⟩

theorem positionProbability_two_fixed (i j : Fin 4) (hij : i ≠ j)
    (y z : Point F) (l : Line F) :
    positionProbability (fun p => ∀ a,
      p a ∈ if a = i then {y} else if a = j then {z} else linePoints l) =
      (Fintype.card F : ℝ)⁻¹^6 := by
  classical
  rw [positionProbability_rectangle]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  fin_cases i <;> fin_cases j <;>
    simp_all [Fin.prod_univ_four, linePoints_card] <;> field_simp

theorem aligned_two_fixed_le (i j : Fin 4) (hij : i ≠ j)
    (y z : Point F) (l : Line F) :
    positionProbability (fun p =>
      (∀ a, OnLine (p a) l) ∧ p i = y ∧ p j = z) ≤
      (Fintype.card F : ℝ)⁻¹^6 := by
  classical
  rw [← positionProbability_two_fixed i j hij y z l]
  apply positionProbability_mono
  rintro p ⟨hl, hi, hj⟩ a
  by_cases hai : a = i
  · simp [hai, hi]
  · by_cases haj : a = j
    · simp [haj, hj, Ne.symm hij]
    · simp [hai, haj, linePoints, hl a]

theorem same_direction_two_positions_lines_le (g : Direction F)
    (i j : Fin 4) (hij : i ≠ j) (l k : Line F) (hlk : l ≠ k) :
    positionProbability (fun p =>
      (∃ c, ∀ a, OnLine (p a) (g,c)) ∧ OnLine (p i) l ∧ OnLine (p j) k) ≤
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  by_cases hgl : g = l.1
  · apply (positionProbability_mono (Q := fun p =>
      (∀ a, OnLine (p a) l) ∧ OnLine (p j) k) ?_).trans
        (aligned_position_on_other_line_le j l k hlk)
    rintro p ⟨⟨c, hc⟩, hi, hj⟩
    have heq : (g,c) = l := eq_of_onLine_same_direction (p i) (g,c) l hgl (hc i) hi
    exact ⟨fun a => by simpa only [heq] using hc a, hj⟩
  · by_cases hgk : g = k.1
    · apply (positionProbability_mono (Q := fun p =>
        (∀ a, OnLine (p a) k) ∧ OnLine (p i) l) ?_).trans
          (aligned_position_on_other_line_le i k l (Ne.symm hlk))
      rintro p ⟨⟨c, hc⟩, hi, hj⟩
      have heq : (g,c) = k := eq_of_onLine_same_direction (p j) (g,c) k hgk (hc j) hj
      exact ⟨fun a => by simpa only [heq] using hc a, hi⟩
    · let P : F → (Fin 4 → Point F) → Prop := fun c p =>
        (∀ a, OnLine (p a) (g,c)) ∧
        p i = lineIntersection (g,c) l ∧ p j = lineIntersection (g,c) k
      have hsub : ∀ p,
          ((∃ c, ∀ a, OnLine (p a) (g,c)) ∧ OnLine (p i) l ∧ OnLine (p j) k) →
          ∃ c, P c p := by
        rintro p ⟨⟨c, hc⟩, hi, hj⟩
        refine ⟨c, hc, ?_, ?_⟩
        · exact common_point_eq_of_lines_ne (g,c) l
            (fun heq => hgl (congrArg Prod.fst heq)) (p i) (lineIntersection (g,c) l)
            (hc i) hi (onLine_lineIntersection_left _ _ hgl)
            (onLine_lineIntersection_right _ _ hgl)
        · exact common_point_eq_of_lines_ne (g,c) k
            (fun heq => hgk (congrArg Prod.fst heq)) (p j) (lineIntersection (g,c) k)
            (hc j) hj (onLine_lineIntersection_left _ _ hgk)
            (onLine_lineIntersection_right _ _ hgk)
      calc
        _ ≤ positionProbability (fun p => ∃ c, P c p) := positionProbability_mono hsub
        _ ≤ (Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹^6 :=
          positionProbability_exists_le_card P _ (fun c =>
            aligned_two_fixed_le i j hij (lineIntersection (g,c) l)
              (lineIntersection (g,c) k) (g,c))
        _ = _ := by
          have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
          field_simp

theorem same_direction_hits_two_lines_le (g : Direction F)
    (l k : Line F) (hlk : l ≠ k) :
    positionProbability (fun p =>
      (∃ c, ∀ a, OnLine (p a) (g,c)) ∧
      ∃ i j : Fin 4, i ≠ j ∧ OnLine (p i) l ∧ OnLine (p j) k) ≤
      12 * (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  let I := {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}
  let P : I → (Fin 4 → Point F) → Prop := fun ij p =>
    (∃ c, ∀ a, OnLine (p a) (g,c)) ∧ OnLine (p ij.1.1) l ∧ OnLine (p ij.1.2) k
  have hcard : Fintype.card I = 12 := by decide
  apply (positionProbability_mono (Q := fun p => ∃ ij, P ij p) ?_).trans
  · simpa only [hcard, Nat.cast_ofNat] using
      positionProbability_exists_le_card P _ (fun ij =>
        same_direction_two_positions_lines_le g ij.1.1 ij.1.2 ij.2 l k hlk)
  · rintro p ⟨hc, i, j, hij, hi, hj⟩
    exact ⟨⟨(i,j), hij⟩, hc, hi, hj⟩

theorem tuple_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (l : Line F) :
    offsetEventProbability {M |
      (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) l} ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  rw [offset_probability_eq T hT (fun p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, OnLine (p i) l)]
  exact same_direction_hits_line_le g l

theorem tuple_contains_point_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (y : Point F) :
    offsetEventProbability {M |
      (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, tuplePoint M T i = y} ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [offset_probability_eq T hT (fun p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, p i = y)]
  exact same_direction_contains_point_le g y

theorem tuple_through_point_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (y : Point F) (k : Line F) (hyk : ¬ OnLine y k) :
    offsetEventProbability {M |
      (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
      ∃ i, OnLine (tuplePoint M T i) k} ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [offset_probability_eq T hT (fun p =>
    (∀ j, OnLine (p j) (lineThrough g y)) ∧ ∃ i, OnLine (p i) k)]
  exact through_point_hits_line_le g y k hyk

theorem tuple_hits_two_lines_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (l k : Line F) (hlk : l ≠ k) :
    offsetEventProbability {M |
      (∃ c, ∀ a, OnLine (tuplePoint M T a) (g,c)) ∧
      ∃ i j : Fin 4, i ≠ j ∧ OnLine (tuplePoint M T i) l ∧ OnLine (tuplePoint M T j) k} ≤
      12 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [offset_probability_eq T hT (fun p =>
    (∃ c, ∀ a, OnLine (p a) (g,c)) ∧
    ∃ i j : Fin 4, i ≠ j ∧ OnLine (p i) l ∧ OnLine (p j) k)]
  exact same_direction_hits_two_lines_le g l k hlk

end
end Balanced.CandidateFreshIncidence

end OAI
