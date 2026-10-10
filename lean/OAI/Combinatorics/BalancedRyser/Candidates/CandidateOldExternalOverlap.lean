import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConditionalMean
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExposedWitness

namespace OAI

namespace Balanced.CandidateOldExternal

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness CandidateExposedWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def targetLine (M : MergedPairs F) (g : Direction F) (T : FourTuple F) : Line F :=
  lineThrough g (tuplePoint M T 0)

theorem successfulOn_target {M : MergedPairs F} {g : Direction F} {T : FourTuple F}
    (hT : T ∈ eligibleTuples g) (hs : M ∈ successfulInDirection T g) :
    SuccessfulOn M T (targetLine M g T) := by
  obtain ⟨hinj, havoid⟩ := (Finset.mem_filter.mp hT).2
  obtain ⟨⟨c, hc⟩, hpoints⟩ := hs
  refine ⟨hinj, havoid, hpoints, ?_⟩
  intro i
  change lineEval g (tuplePoint M T i) = lineEval g (tuplePoint M T 0)
  exact (hc i).trans (hc 0).symm

def IsExternalWitness (M : MergedPairs F) (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (d e : Direction F) (x : Point F) : Prop :=
  OnLine x (targetLine M g T) ∧ x ∉ designated M ⟨targetLine M g T, T⟩ ∧
  i ≠ j ∧ d ≠ e ∧ d ≠ g ∧ e ≠ g ∧ d ∉ generatorSet T ∧ e ∉ generatorSet T ∧
  PairWitness M d x (tuplePoint M T i) ∧ PairWitness M e x (tuplePoint M T j)

abbrev WitnessKey (F : Type*) :=
  (FourTuple F × (Fin 4 × Fin 4)) × (Direction F × Direction F)

abbrev WitnessLabel (F : Type*) := WitnessKey F × Point F

def oldOverlapKeys (g : Direction F) (D : Finset (Direction F)) (M : MergedPairs F) :
    Finset (WitnessKey F) :=
  (((((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card)).filter
    (fun T => M ∈ successfulInDirection T g)).product Finset.univ).product (D.product D))

def oldOverlapWitnesses (g : Direction F) (D : Finset (Direction F)) (M : MergedPairs F) :
    Finset (WitnessLabel F) :=
  ((oldOverlapKeys g D M).product Finset.univ).filter (fun w =>
    IsExternalWitness M g w.1.1.1 w.1.1.2.1 w.1.1.2.2 w.1.2.1 w.1.2.2 w.2)

theorem mem_oldOverlapWitnesses_iff (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) (T : FourTuple F) (i j : Fin 4) (d e : Direction F) (x : Point F) :
    (((T, (i,j)), (d,e)), x) ∈ oldOverlapWitnesses g D M ↔
      T ∈ eligibleTuples g ∧ 0 < (exposedTupleIndices T D).card ∧
      M ∈ successfulInDirection T g ∧ d ∈ D ∧ e ∈ D ∧
      IsExternalWitness M g T i j d e x := by
  simp only [oldOverlapWitnesses, oldOverlapKeys, Finset.product_eq_sprod,
    Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  tauto

theorem key_injective_on_oldOverlapWitnesses (g : Direction F)
    (D : Finset (Direction F)) (M : MergedPairs F) :
    Set.InjOn (Prod.fst : WitnessLabel F → WitnessKey F) (oldOverlapWitnesses g D M) := by
  rintro ⟨key, x⟩ hx ⟨key', y⟩ hy hkey
  change key = key' at hkey
  subst key'
  rcases key with ⟨⟨T, ⟨i,j⟩⟩, ⟨d,e⟩⟩
  rcases (mem_oldOverlapWitnesses_iff g D M T i j d e x).mp hx with
    ⟨hT, _, hs, _, _, hxline, hex, _, _, hd, _, _, _, hdx, _⟩
  rcases (mem_oldOverlapWitnesses_iff g D M T i j d e y).mp hy with
    ⟨_, _, _, _, _, hyline, _, _, _, _, _, _, _, hdy, _⟩
  have hxy := external_point_unique (successfulOn_target hT hs) hd i hxline hyline hex hdx hdy
  exact congrArg (fun z : Point F => (((T, (i,j)), (d,e)), z)) hxy

theorem card_oldOverlapWitnesses_le (g : Direction F)
    (D : Finset (Direction F)) (M : MergedPairs F) :
    (oldOverlapWitnesses g D M).card ≤
      16 * D.card ^ 2 * overlappingTupleCount g D M := by
  calc
    (oldOverlapWitnesses g D M).card ≤ (oldOverlapKeys g D M).card :=
      Finset.card_le_card_of_injOn Prod.fst
        (fun w hw => (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1)
        (key_injective_on_oldOverlapWitnesses g D M)
    _ = _ := by
      simp only [oldOverlapKeys, Finset.product_eq_sprod, Finset.card_product,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, overlappingTupleCount]
      ring

theorem exists_mem_of_old_external {g : Direction F} {D : Finset (Direction F)}
    {M : MergedPairs F} {T : FourTuple F} (hT : T ∈ eligibleTuples g)
    (hover : 0 < (exposedTupleIndices T D).card)
    (hs : M ∈ successfulInDirection T g)
    (h : ∃ x i j d e, d ∈ D ∧ e ∈ D ∧ IsExternalWitness M g T i j d e x) :
    ∃ w ∈ oldOverlapWitnesses g D M, w.1.1.1 = T := by
  obtain ⟨x,i,j,d,e,hd,he,hw⟩ := h
  exact ⟨(((T,(i,j)),(d,e)),x),
    (mem_oldOverlapWitnesses_iff g D M T i j d e x).mpr ⟨hT,hover,hs,hd,he,hw⟩, rfl⟩

theorem expected_oldOverlapWitnesses_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (exposedLaw D a M).toReal *
      ((oldOverlapWitnesses g D M).card : ℝ)) ≤
      262144 * (m : ℝ)^2 * ((m : ℝ) + 1)^4 := by
  let : MeasurableSpace F := ⊤
  have hmean := conditional_overlappingTupleCount_le g D a m hD
  rw [PMF.integral_eq_sum] at hmean
  simp only [smul_eq_mul] at hmean
  have hcard (M : MergedPairs F) : ((oldOverlapWitnesses g D M).card : ℝ) ≤
      (16 * (m : ℝ)^2) * (overlappingTupleCount g D M : ℝ) := by
    exact_mod_cast (card_oldOverlapWitnesses_le g D M).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hD 2)))
  calc
    _ ≤ ∑ M : MergedPairs F, (exposedLaw D a M).toReal *
        ((16 * (m : ℝ)^2) * (overlappingTupleCount g D M : ℝ)) := by
      exact Finset.sum_le_sum (fun M _ =>
        mul_le_mul_of_nonneg_left (hcard M) ENNReal.toReal_nonneg)
    _ = (16 * (m : ℝ)^2) * ∑ M : MergedPairs F, (exposedLaw D a M).toReal *
        (overlappingTupleCount g D M : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      ring
    _ ≤ (16 * (m : ℝ)^2) * (16384 * ((m : ℝ) + 1)^4) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

def oldOverlapPrescriptions (g : Direction F) (D : Finset (Direction F)) :
    Finset (WitnessKey F) :=
  ((((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card)).product
    Finset.univ).product (D.product D))

def keyEvent (g : Direction F) (k : WitnessKey F) : Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection k.1.1 g ∧
    ∃ x, IsExternalWitness M g k.1.1 k.1.2.1 k.1.2.2 k.2.1 k.2.2 x}

theorem keyWitnesses_eq_image (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    (oldOverlapPrescriptions g D).filter (fun k => M ∈ keyEvent g k) =
      (oldOverlapWitnesses g D M).image Prod.fst := by
  ext k
  rcases k with ⟨⟨T, ⟨i,j⟩⟩, ⟨d,e⟩⟩
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hbase, hs, x, hx⟩
    have hb : T ∈ eligibleTuples g ∧ 0 < (exposedTupleIndices T D).card ∧
        d ∈ D ∧ e ∈ D := by
      simpa only [oldOverlapPrescriptions, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_filter, Finset.mem_univ, and_true, and_assoc] using hbase
    exact Finset.mem_image.mpr ⟨(((T,(i,j)),(d,e)),x),
      (mem_oldOverlapWitnesses_iff g D M T i j d e x).mpr
        ⟨hb.1,hb.2.1,hs,hb.2.2.1,hb.2.2.2,hx⟩, rfl⟩
  · intro hk
    obtain ⟨⟨k,x⟩, hx, heq⟩ := Finset.mem_image.mp hk
    change k = ((T,(i,j)),(d,e)) at heq
    subst k
    obtain ⟨hT,hover,hs,hd,he,hw⟩ :=
      (mem_oldOverlapWitnesses_iff g D M T i j d e x).mp hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hs, x, hw⟩
    simp only [oldOverlapPrescriptions, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, and_true]
    exact ⟨⟨hT,hover⟩,hd,he⟩

theorem keyWitnesses_card (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    ((oldOverlapPrescriptions g D).filter (fun k => M ∈ keyEvent g k)).card =
      (oldOverlapWitnesses g D M).card := by
  rw [keyWitnesses_eq_image]
  exact Finset.card_image_of_injOn (key_injective_on_oldOverlapWitnesses g D M)

theorem sum_oldOverlapWitness_probability_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ k ∈ oldOverlapPrescriptions g D,
      ((exposedLaw D a).toOuterMeasure (keyEvent g k)).toReal) ≤
      262144 * (m : ℝ)^2 * ((m : ℝ) + 1)^4 := by
  let : MeasurableSpace F := ⊤
  have h := integral_eventCount_eq_sum (exposedLaw D a)
    (oldOverlapPrescriptions g D) (keyEvent g)
  rw [PMF.integral_eq_sum] at h
  simp only [smul_eq_mul, keyWitnesses_card] at h
  rw [← h]
  exact expected_oldOverlapWitnesses_le g D a m hD

end
end Balanced.CandidateOldExternal

end OAI
