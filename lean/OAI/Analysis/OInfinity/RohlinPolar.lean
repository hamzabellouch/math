import OAI.Analysis.OInfinity.RohlinUnitarity

namespace OAI

/-! # Polar correction of the finite Rohlin sum

Both Gram defects are used. An element with small initial and final Gram
defects is invertible; continuous functional calculus then corrects it to a
nearby unitary. This step does not supply the tower commutator estimates.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma isUnit_of_two_gram_units (x : E)
    (hi : IsUnit (star x * x)) (hf : IsUnit (x * star x)) : IsUnit x := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hf
  apply isUnit_iff_exists_and_exists.mpr
  constructor
  · refine ⟨star x * (↑b⁻¹ : E), ?_⟩
    calc
      x * (star x * (↑b⁻¹ : E)) = (x * star x) * (↑b⁻¹ : E) := by rw [mul_assoc]
      _ = (b : E) * (↑b⁻¹ : E) := by rw [hb]
      _ = 1 := b.val_inv
  · refine ⟨(↑a⁻¹ : E) * star x, ?_⟩
    calc
      ((↑a⁻¹ : E) * star x) * x = (↑a⁻¹ : E) * (star x * x) := by rw [mul_assoc]
      _ = (↑a⁻¹ : E) * (a : E) := by rw [ha]
      _ = 1 := a.inv_val

lemma isUnit_of_norm_sub_one_lt (a : E) (ha : ‖a - 1‖ < 1) : IsUnit a := by
  have h : ‖1 - a‖ < 1 := by rwa [norm_sub_rev]
  convert isUnit_one_sub_of_norm_lt_one h using 1
  noncomm_ring

local instance rohlinPolarOrder : PartialOrder E := CStarAlgebra.spectralOrder E
local instance rohlinPolarStarOrder : StarOrderedRing E := CStarAlgebra.spectralOrderedRing E

lemma exists_polar_unitary_of_two_gram_units (x : E)
    (hi : IsUnit (star x * x)) (hf : IsUnit (x * star x)) :
    ∃ u : unitary E, (u : E) = x * CFC.rpow (star x * x) (-1 / 2 : ℝ) := by
  let a := star x * x
  let b := CFC.rpow a (-1 / 2 : ℝ)
  have ha : 0 ≤ a := star_mul_self_nonneg x
  have hai : IsUnit a := hi
  have hb : IsSelfAdjoint b := (CFC.rpow_nonneg (a := a) (y := (-1 / 2 : ℝ))).isSelfAdjoint
  have hbi : IsUnit b := hi.cfcRpow (-1 / 2 : ℝ) ha
  have hx : IsUnit x := isUnit_of_two_gram_units x hi hf
  have hpow : (b * a) * b = 1 := by
    change (CFC.rpow a (-1 / 2 : ℝ) * a) * CFC.rpow a (-1 / 2 : ℝ) = 1
    conv_lhs => lhs; rhs; rw [← CFC.rpow_one a ha]
    simp only [CFC.rpow_eq_pow]
    rw [← CFC.rpow_add hai, ← CFC.rpow_add hai]
    norm_num [CFC.rpow_zero a ha]
  have hp : star (x * b) * (x * b) = 1 := by
    rw [star_mul, hb.star_eq]
    calc
      _ = (b * a) * b := by dsimp [a]; noncomm_ring
      _ = 1 := hpow
  exact ⟨⟨x * b, (hx.mul hbi).mem_unitary_of_star_mul_self hp⟩, rfl⟩

/-- An arbitrarily small polar correction follows from a sufficiently small
initial Gram defect and a final Gram defect less than one. -/
lemma exists_near_unitary_of_two_gram_errors [Nontrivial E] (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E,
      ‖star x * x - 1‖ < δ → ‖x * star x - 1‖ < 1 →
      ∃ u : unitary E, ‖(u : E) - x‖ < ε := by
  have hcont : ContinuousWithinAt (fun a : E => CFC.rpow a (-1 / 2 : ℝ))
      {a | IsStrictlyPositive a} 1 :=
    CFC.continuousOn_rpow (-1 / 2 : ℝ) 1 (by exact isStrictlyPositive_one)
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousWithinAt_iff.mp hcont (ε / 2) (half_pos hε)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro x hix hfx
  have hi1 : ‖star x * x - 1‖ < 1 := hix.trans_le (min_le_right _ _)
  have hi : IsUnit (star x * x) := isUnit_of_norm_sub_one_lt _ hi1
  have hf : IsUnit (x * star x) := isUnit_of_norm_sub_one_lt _ hfx
  have ha : IsStrictlyPositive (star x * x) := hi.isStrictlyPositive (star_mul_self_nonneg x)
  have hbsmall : ‖CFC.rpow (star x * x) (-1 / 2 : ℝ) - 1‖ < ε / 2 := by
    simpa only [dist_eq_norm, CFC.rpow_eq_pow, CFC.one_rpow] using hb ha (show dist (star x * x) 1 < δ from
      by rw [dist_eq_norm]; exact hix.trans_le (min_le_left _ _))
  have hxnorm : ‖x‖ < 2 := by
    have hh : ‖star x * x‖ < 2 := by
      calc
        _ ≤ ‖star x * x - 1‖ + ‖(1 : E)‖ := norm_le_norm_sub_add _ _
        _ = ‖star x * x - 1‖ + 1 := by rw [norm_one]
        _ < 2 := by linarith
    rw [CStarRing.norm_star_mul_self] at hh
    nlinarith [norm_nonneg x]
  obtain ⟨u, hu⟩ := exists_polar_unitary_of_two_gram_units x hi hf
  refine ⟨u, ?_⟩
  rw [hu]
  calc
    _ = ‖x * (CFC.rpow (star x * x) (-1 / 2 : ℝ) - 1)‖ := by rw [mul_sub, mul_one]
    _ ≤ ‖x‖ * ‖CFC.rpow (star x * x) (-1 / 2 : ℝ) - 1‖ := norm_mul_le _ _
    _ ≤ 2 * ‖CFC.rpow (star x * x) (-1 / 2 : ℝ) - 1‖ :=
      mul_le_mul_of_nonneg_right hxnorm.le (norm_nonneg _)
    _ < 2 * (ε / 2) := mul_lt_mul_of_pos_left hbsmall (by norm_num)
    _ = ε := by ring

end WeakPureInfiniteness

end

end OAI
