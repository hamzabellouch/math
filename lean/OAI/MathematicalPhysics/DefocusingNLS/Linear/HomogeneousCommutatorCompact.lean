import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorDecay
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Compactness of the actual frequency-localized commutator

The row functionals and the integrable Schwartz majorant give strong L²
convergence for every bounded weakly null sequence in the exact Y space.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem row_norm_le_of_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (N : ℕ) (j : Fin N → Fin 12) (V χ : 𝓢(E, ℂ)) (ξ : E) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ η : E, ‖homogeneousCommutatorRowKernel N j V χ ξ η‖ ≤ A)
    (u : HomogeneousY a k) :
    ‖homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ u‖ ≤
      A * Real.sqrt (∫ η : E, (homogeneousFourierWeight a k η)⁻¹) * ‖u‖ := by
  have hu := integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)
  have hn : Real.sqrt (∫ η : E, ‖u η‖ ^ 2 ∂homogeneousFourierMeasure a k) = ‖u‖ := by
    rw [Lp.norm_def, (Lp.memLp u).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num
  rw [hn] at hu
  have hm := integral_mono_of_nonneg (ae_of_all _ (fun η : E => norm_nonneg
    (homogeneousCommutatorRowKernel N j V χ ξ η * u η)))
    (hu.1.norm.const_mul A) (ae_of_all _ (fun η => by
      change ‖homogeneousCommutatorRowKernel N j V χ ξ η * u η‖ ≤ A * ‖u η‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound η) (norm_nonneg _)))
  calc
    _ ≤ ∫ η : E, ‖homogeneousCommutatorRowKernel N j V χ ξ η * u η‖ :=
      norm_integral_le_integral_norm _
    _ ≤ A * ∫ η : E, ‖u η‖ := hm.trans_eq (integral_const_mul _ _)
    _ ≤ A * (Real.sqrt (∫ η : E, (homogeneousFourierWeight a k η)⁻¹) * ‖u‖) :=
      mul_le_mul_of_nonneg_left hu.2 hA
    _ = _ := by ring

private theorem row_aestronglyMeasurable (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (N : ℕ) (j : Fin N → Fin 12) (V χ : 𝓢(E, ℂ)) (u : HomogeneousY a k) :
    AEStronglyMeasurable
      (fun ξ : E => homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ u) volume := by
  have hK : Continuous (fun p : E × E => homogeneousCommutatorRowKernel N j V χ p.1 p.2) := by
    unfold homogeneousCommutatorRowKernel homogeneousOrderedSymbol
    fun_prop
  have hu : AEStronglyMeasurable (fun p : E × E => u p.2) (volume.prod volume) :=
    ((Lp.aestronglyMeasurable u).mono_ac
      (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk)).comp_snd
  exact (hK.aestronglyMeasurable.mul hu).integral_prod_right'

theorem tendsto_homogeneousCommutator_cutoff_L2 (a k M R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R)
    (N : ℕ) (j : Fin N → Fin 12) (V χ : 𝓢(E, ℂ))
    (hχ : ∀ η : E, R < ‖η‖ → χ η = 0)
    (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ξ : E,
      ‖homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ (u n)‖ ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hc⟩ := homogeneousCommutatorRow_decay N j V χ R hR hχ
  let D := Real.sqrt (∫ η : E, (homogeneousFourierWeight a k η)⁻¹)
  let B : E → ℝ := fun ξ => (C * D * M) ^ 2 * (1 + ‖ξ‖) ^ (-(28 : ℝ))
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
  have hpow (ξ : E) : (((1 + ‖ξ‖) ^ (14 : ℕ))⁻¹) ^ 2 = (1 + ‖ξ‖) ^ (-(28 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_ofNat, ← inv_pow, ← pow_mul]
    norm_num
  have hb (n : ℕ) (ξ : E) :
      ‖‖homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ (u n)‖ ^ 2‖ ≤ B ξ := by
    have hr := (row_norm_le_of_bound a k ha ha1 hk N j V χ ξ
      (C * ((1 + ‖ξ‖) ^ (14 : ℕ))⁻¹) (by positivity) (hc ξ) (u n)).trans
      (mul_le_mul_of_nonneg_left (hu n) (mul_nonneg (by positivity) hD))
    have hs := pow_le_pow_left₀ (norm_nonneg _) hr 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply hs.trans_eq
    dsimp only [B, D]
    rw [mul_pow, mul_pow, mul_pow, hpow]
    ring
  have hB : Integrable B := by
    apply Integrable.const_mul
    apply integrable_one_add_norm
    norm_num
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun ξ : E => ‖homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ (u n)‖ ^ 2) volume :=
    (row_aestronglyMeasurable a k ha ha1 hk N j V χ (u n)).norm.pow 2
  have hp (ξ : E) : Tendsto
      (fun n => ‖homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ (u n)‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (tendsto_homogeneousCommutatorRow_of_weakNull a k ha ha1 hk N j V χ ξ u hweak).norm.pow 2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence B hm hB
    (fun n => ae_of_all _ (hb n)) (ae_of_all _ hp)

end DefocusingNLS

end OAI
