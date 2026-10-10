import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalMap

namespace OAI

/-! Lowering the high Fourier exponent preserves the physical representative. -/

open MeasureTheory
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousFourierWeight_lower (a j k : ℝ) (ha : 0 < a)
    (hj : 8 < j) (hjk : j ≤ k) (ξ : E) :
    homogeneousFourierWeight a j ξ ≤ 2 * homogeneousFourierWeight a k ξ := by
  have hp : ‖ξ‖ ^ (2*j) ≤ ‖ξ‖ ^ (2*(6-a)) + ‖ξ‖ ^ (2*k) := by
    by_cases h : ‖ξ‖ ≤ 1
    · by_cases hzero : ‖ξ‖ = 0
      · simp only [hzero, Real.zero_rpow (show 2*j ≠ 0 by linarith)]
        positivity
      · have hpow : ‖ξ‖ ^ (2*j) ≤ ‖ξ‖ ^ (2*(6-a)) :=
          Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm hzero)) h
            (by linarith)
        exact hpow.trans (le_add_of_nonneg_right (by positivity))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by linarith)).trans
        (le_add_of_nonneg_left (by positivity))
  unfold homogeneousFourierWeight
  have h0 : 0 ≤ ‖ξ‖ ^ (2*(6-a)) := by positivity
  have h1 : 0 ≤ ‖ξ‖ ^ (2*k) := by positivity
  have hsum : ‖ξ‖ ^ (2*(6-a)) + ‖ξ‖ ^ (2*j) ≤
      2 * (‖ξ‖ ^ (2*(6-a)) + ‖ξ‖ ^ (2*k)) := by linarith
  calc
    _ ≤ ((2*Real.pi)^12)⁻¹ * (2*(‖ξ‖ ^ (2*(6-a)) + ‖ξ‖ ^ (2*k))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem homogeneous_memLp_lower (a j k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hj : 8 < j) (hjk : j ≤ k) (u : HomogeneousY a k) :
    MemLp (fun ξ => u ξ) 2 (homogeneousFourierMeasure a j) := by
  have hk : 8 < k := hj.trans_le hjk
  have hmj := (continuous_homogeneousFourierWeight a j ha1 hj).measurable
  have hmk := (continuous_homogeneousFourierWeight a k ha1 hk).measurable
  have hmeas := (Lp.memLp u).aestronglyMeasurable.mono_ac
    (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk)
  have hum : AEStronglyMeasurable (fun ξ => u ξ) (homogeneousFourierMeasure a j) :=
    hmeas.mono_ac (withDensity_absolutelyContinuous volume _)
  apply (memLp_two_iff_integrable_sq_norm hum).mpr
  apply (integrable_withDensity_iff_integrable_smul' (μ := volume)
    hmj.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  simp only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a j _), smul_eq_mul]
  have hsq := (memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp
    (Lp.memLp u)
  have hw := (integrable_withDensity_iff_integrable_smul' (μ := volume)
    hmk.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hsq
  simp only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a k _), smul_eq_mul] at hw
  apply (hw.const_mul 2).mono' (hmj.aestronglyMeasurable.mul (hmeas.norm.pow 2))
  filter_upwards [] with ξ
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (homogeneousFourierWeight_nonneg a j ξ) (sq_nonneg _))]
  calc
    _ ≤ (2 * homogeneousFourierWeight a k ξ) * ‖u ξ‖^2 :=
      mul_le_mul_of_nonneg_right (homogeneousFourierWeight_lower a j k ha hj hjk ξ)
        (sq_nonneg _)
    _ = _ := by ring

theorem exists_homogeneousLowerOrder (a j k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hj : 8 < j) (hjk : j ≤ k) (u : HomogeneousY a k) :
    ∃ v : HomogeneousY a j, ∀ x : E,
      homogeneousPhysicalCLM a j ha ha1 hj v x =
        homogeneousPhysicalCLM a k ha ha1 (hj.trans_le hjk) u x := by
  let h := homogeneous_memLp_lower a j k ha ha1 hj hjk u
  refine ⟨h.toLp (fun ξ => u ξ), ?_⟩
  have he := h.coeFn_toLp
  have hev := he.filter_mono
    (volume_absolutelyContinuous_homogeneousFourierMeasure a j ha1 hj).ae_le
  intro x
  exact congrFun (inverseRadianFourier_congr_ae hev) x

end DefocusingNLS

end OAI
