import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExposure
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateWitnessProbability
import OAI.Combinatorics.BalancedRyser.Probability.FreshTupleWitness

namespace OAI

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable

namespace Balanced.FreshRandomWitness

open FreshWitnessProbability FreshTupleWitness CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exposedLaw_eq_candidate (D : Finset (Direction F)) (a : MergedPairs F) :
    exposedLaw D a = CandidateExposure.exposedLaw D a := rfl

theorem exposedLaw_eq_uniform_fiber (D : Finset (Direction F)) (a : MergedPairs F) :
    exposedLaw D a =
      (PMF.uniformOfFintype
        (ConditionalRestriction.FixedArray (fun d => d ∈ D) a)).map Subtype.val := by
  simp only [exposedLaw, PartialAlignment.offsetLaw_eq_uniform]
  exact @Balanced.uniform_filter_eq_subtype_map (MergedPairs F) inferInstance inferInstance
    {M | ∀ d, d ∈ D → M d = a d}
    (inferInstance : Fintype (ConditionalRestriction.FixedArray (fun d => d ∈ D) a))
    (inferInstance : Nonempty (ConditionalRestriction.FixedArray (fun d => d ∈ D) a))
    ⟨a, by intro d hd; rfl, PMF.mem_support_uniformOfFintype _⟩

theorem prescription_probability (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hd : d ∉ D)
    (E : MergedPairs F → Prop) (b : MergedPairs F → Bool → F)
    (hE : ∀ M v, E (Function.update M d v) ↔ E M)
    (hb : ∀ M v, b (Function.update M d v) = b M) :
    ((exposedLaw D a).toOuterMeasure {M | E M ∧ M d = b M}).toReal =
      ((exposedLaw D a).toOuterMeasure {M | E M}).toReal /
        (Fintype.card F : ℝ)^2 := by
  rw [exposedLaw_eq_uniform_fiber]
  simp only [PMF.toOuterMeasure_map_apply]
  have h := FreshCoordinate.probability_prescription_on_subtype d
    (fun M : MergedPairs F => ∀ t, t ∈ D → M t = a t) E b
    (fixed_coordinates_update_invariant (fun t => t ∈ D) a d hd) hE hb
  change ((PMF.uniformOfFintype
    (ConditionalRestriction.FixedArray (fun t => t ∈ D) a)).toOuterMeasure
      {M | E M.val ∧ M.val d = b M.val}).toReal =
    ((PMF.uniformOfFintype
    (ConditionalRestriction.FixedArray (fun t => t ∈ D) a)).toOuterMeasure
      {M | E M.val}).toReal / (Fintype.card F : ℝ)^2
  have hcard : (Fintype.card (Bool → F) : ℝ) = (Fintype.card F : ℝ)^2 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  rw [hcard] at h
  simpa only [PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_eq_nat_card] using h

theorem oriented_pair_probability (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hd : d ∉ D) (E : MergedPairs F → Prop)
    (x y : MergedPairs F → Point F) (σ : Bool)
    (hE : ∀ M v, E (Function.update M d v) ↔ E M)
    (hx : ∀ M v, x (Function.update M d v) = x M)
    (hy : ∀ M v, y (Function.update M d v) = y M) :
    ((exposedLaw D a).toOuterMeasure {M | E M ∧
      OnLine (x M) (constituent M d σ) ∧
      OnLine (y M) (constituent M d (!σ))}).toReal =
      ((exposedLaw D a).toOuterMeasure {M | E M}).toReal /
        (Fintype.card F : ℝ)^2 := by
  have h := prescription_probability D a d hd E
    (fun M => pairPrescription d (x M) (y M) σ) hE
    (by intro M v; rw [hx, hy])
  simpa only [pairPrescription_iff] using h

theorem pairWitness_probability_le (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hd : d ∉ D) (E : MergedPairs F → Prop)
    (x y : MergedPairs F → Point F)
    (hE : ∀ M v, E (Function.update M d v) ↔ E M)
    (hx : ∀ M v, x (Function.update M d v) = x M)
    (hy : ∀ M v, y (Function.update M d v) = y M) :
    ((exposedLaw D a).toOuterMeasure
      {M | E M ∧ PairWitness M d (x M) (y M)}).toReal ≤
      2 * ((exposedLaw D a).toOuterMeasure {M | E M}).toReal /
        (Fintype.card F : ℝ)^2 := by
  have hevent : {M : MergedPairs F | E M ∧ PairWitness M d (x M) (y M)} =
      {M | ∃ σ : Bool, E M ∧ OnLine (x M) (constituent M d σ) ∧
        OnLine (y M) (constituent M d (!σ))} := by
    ext M
    constructor
    · rintro ⟨hEM, σ, hxM, hyM⟩
      exact ⟨σ, hEM, hxM, hyM⟩
    · rintro ⟨σ, hEM, hxM, hyM⟩
      exact ⟨hEM, σ, hxM, hyM⟩
  rw [hevent]
  calc
    _ ≤ ∑ σ : Bool, ((exposedLaw D a).toOuterMeasure
        {M | E M ∧ OnLine (x M) (constituent M d σ) ∧
          OnLine (y M) (constituent M d (!σ))}).toReal :=
      probability_exists_le_sum _ _
    _ = _ := by
      simp only [oriented_pair_probability D a d hd E x y _ hE hx hy,
        Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
      ring

theorem sum_pairWitness_probability_le (D : Finset (Direction F)) (a : MergedPairs F)
    (U : Finset (Direction F)) (hfresh : ∀ d ∈ U, d ∉ D)
    (E : MergedPairs F → Prop) (x y : MergedPairs F → Point F)
    (hE : ∀ d ∈ U, ∀ M v, E (Function.update M d v) ↔ E M)
    (hx : ∀ d ∈ U, ∀ M v, x (Function.update M d v) = x M)
    (hy : ∀ d ∈ U, ∀ M v, y (Function.update M d v) = y M) :
    (∑ d ∈ U, ((exposedLaw D a).toOuterMeasure
      {M | E M ∧ PairWitness M d (x M) (y M)}).toReal) ≤
      4 * ((exposedLaw D a).toOuterMeasure {M | E M}).toReal /
        Fintype.card F := by
  let p := ((exposedLaw D a).toOuterMeasure {M | E M}).toReal
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hU : (U.card : ℝ) ≤ (Fintype.card F : ℝ) + 1 := by
    exact_mod_cast (show U.card ≤ Fintype.card F + 1 by
      simpa only [Direction, Fintype.card_option] using Finset.card_le_univ U)
  calc
    _ ≤ ∑ _d ∈ U, 2 * p / (Fintype.card F : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro d hd
      exact pairWitness_probability_le D a d (hfresh d hd) E x y
        (hE d hd) (hx d hd) (hy d hd)
    _ = (U.card : ℝ) * (2 * p / (Fintype.card F : ℝ)^2) := by simp
    _ ≤ 4 * p / Fintype.card F := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
      have hcancel : (4 * p / (Fintype.card F : ℝ)) * (Fintype.card F : ℝ)^2 =
          4 * p * Fintype.card F := by field_simp
      rw [hcancel]
      nlinarith [mul_nonneg hp (sub_nonneg.mpr hU),
        mul_nonneg hp (sub_nonneg.mpr hq1)]

end Balanced.FreshRandomWitness

end

end OAI
