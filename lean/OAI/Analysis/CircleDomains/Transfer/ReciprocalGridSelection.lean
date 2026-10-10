import OAI.Analysis.CircleDomains.Probability.RandomShifts
import OAI.Analysis.CircleDomains.Selection.GoodSample
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-!
# Selecting an actual reciprocal-integer grid

The grid spacing must be `1/N` so that the staircases respect period one.
The laws of the uniform shifts change with the spacing. This selection
uses those actual product laws, keeps any prescribed conull compatibility
event, and makes both the wedge cost and scaled terminal count small.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

noncomputable def reciprocalGridStep (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

noncomputable def reciprocalGridLaw (n N : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => shiftLaw (reciprocalGridStep N))

theorem reciprocalGridStep_pos (N : ℕ) : 0 < reciprocalGridStep N := by
  unfold reciprocalGridStep
  positivity

theorem reciprocalGridStep_le_one (N : ℕ) : reciprocalGridStep N ≤ 1 := by
  unfold reciprocalGridStep
  apply (div_le_one (by positivity : 0 < (N : ℝ) + 1)).mpr
  exact le_add_of_nonneg_left (Nat.cast_nonneg N)

theorem reciprocalGridStep_mul_denominator (N : ℕ) :
    reciprocalGridStep N * ((N : ℝ) + 1) = 1 := by
  unfold reciprocalGridStep
  exact div_mul_cancel₀ 1 (by positivity)

theorem reciprocalGridStep_tendsto_zero :
    Tendsto reciprocalGridStep atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem reciprocalGridLaw_isProbabilityMeasure (n N : ℕ) :
    IsProbabilityMeasure (reciprocalGridLaw n N) := by
  let := shiftLaw_isProbabilityMeasure (reciprocalGridStep_pos N)
  unfold reciprocalGridLaw
  infer_instance

/-- Simultaneous selection with the exact laws and exact reciprocal
spacings used in finite transfer. -/
theorem exists_actual_compatible_good_grid {n : ℕ}
    (W J : ℕ → (Fin n → ℝ) → ℝ) (P : ℕ → (Fin n → ℝ) → Prop)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hWi : ∀ N, Integrable (W N) (reciprocalGridLaw n N))
    (hJi : ∀ N, Integrable (J N) (reciprocalGridLaw n N))
    (hW0 : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ W N θ)
    (hJ0 : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ J N θ)
    (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    (hWmean : ∀ᶠ N in atTop, (∫ θ, W N θ ∂reciprocalGridLaw n N) < η / 4)
    (hJmean : Tendsto
      (fun N => reciprocalGridStep N ^ 2 * (∫ θ, J N θ ∂reciprocalGridLaw n N))
      atTop (𝓝 0)) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < δ ∧ P N θ ∧ W N θ < η ∧
      reciprocalGridStep N * Real.sqrt (J N θ) < η := by
  have hη2 : 0 < η ^ 2 := sq_pos_of_pos hη
  have hsmall : ∀ᶠ N in atTop,
      reciprocalGridStep N < δ ∧
      (∫ θ, W N θ ∂reciprocalGridLaw n N) < η / 4 ∧
      reciprocalGridStep N ^ 2 * (∫ θ, J N θ ∂reciprocalGridLaw n N) < η ^ 2 / 4 := by
    filter_upwards [reciprocalGridStep_tendsto_zero.eventually_lt_const hδ, hWmean,
      hJmean.eventually_lt_const (by positivity : 0 < η ^ 2 / 4)] with N hN hW hJ
    exact ⟨hN, hW, hJ⟩
  obtain ⟨N, hN, hW, hJ⟩ := hsmall.exists
  let := reciprocalGridLaw_isProbabilityMeasure n N
  have hGi : Integrable (fun θ => reciprocalGridStep N ^ 2 * J N θ)
      (reciprocalGridLaw n N) := (hJi N).const_mul _
  have hG0 : ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ reciprocalGridStep N ^ 2 * J N θ :=
    (hJ0 N).mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ)
  have hWr : (∫ θ, W N θ ∂reciprocalGridLaw n N) / η < (1 : ℝ) / 4 :=
    (div_lt_iff₀ hη).mpr (by nlinarith)
  have hJr : (∫ θ, reciprocalGridStep N ^ 2 * J N θ ∂reciprocalGridLaw n N) / η ^ 2 <
      (1 : ℝ) / 4 := by
    rw [integral_const_mul]
    exact (div_lt_iff₀ hη2).mpr (by nlinarith)
  obtain ⟨θ, hθP, hθW, hθJ⟩ := exists_good_sample hη hη2 (hWi N) hGi
    (hW0 N) hG0 ((hP N).and (hJ0 N)) (by linarith)
  refine ⟨N, θ, hN, hθP.1, hθW, ?_⟩
  have hsquare : (reciprocalGridStep N * Real.sqrt (J N θ)) ^ 2 < η ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt hθP.2]
  exact (sq_lt_sq₀
    (mul_nonneg (reciprocalGridStep_pos N).le (Real.sqrt_nonneg _)) hη.le).mp hsquare

end CircleDomainRigidity.FiniteTransfer

end OAI
