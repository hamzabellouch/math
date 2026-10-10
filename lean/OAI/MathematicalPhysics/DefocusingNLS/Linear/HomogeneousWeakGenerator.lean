import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeTestBounds
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGeneratorCoordinates
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace OAI

/-! # The weak Fourier equation for the actual free generator

This is the distributional identity behind the physical operator
i Delta - x dot grad / 2 - a + i b. The statement uses ordinary Lebesgue
integrals of the faithful Fourier representative and Schwartz tests.
-/

open Set Filter MeasureTheory Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem hasDerivAt_homogeneousFourierPairing_free (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u : HomogeneousY a k) (φ : 𝓢(E, ℂ)) :
    HasDerivAt (fun t : ℝ => homogeneousFourierPairing a k ha ha1 hk φ
      (homogeneousFreeOperator a b k t ha ha1 hk u))
      (∫ ξ : E, u ξ * homogeneousFreeDualDerivative a b 0 φ ξ) 0 := by
  have hu := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)).1
  have hm : AEStronglyMeasurable (fun ξ : E => u ξ) volume := hu.aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (x₀ := (0 : ℝ)) (s := Ioo (-1 : ℝ) 1)
    (F := fun t ξ => u ξ * homogeneousFreeDualTest a b t φ ξ)
    (F' := fun t ξ => u ξ * homogeneousFreeDualDerivative a b t φ ξ)
    (bound := fun ξ => (Real.exp a * homogeneousFreeTestBound a b φ) * ‖u ξ‖)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => hm.mul (homogeneousFreeDualTest a b t φ).continuous.aestronglyMeasurable)
    (integrable_homogeneousFourier_test a k ha ha1 hk u (homogeneousFreeDualTest a b 0 φ))
    (hm.mul (continuous_homogeneousFreeDualDerivative a b 0 φ).aestronglyMeasurable)
    (by
      filter_upwards [] with ξ t ht
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_left (homogeneousFreeDualDerivative_norm_le a b t φ ξ)
        (norm_nonneg _)).trans
      have he : Real.exp (-a * t) ≤ Real.exp a := by
        apply Real.exp_le_exp.mpr
        nlinarith [ht.1]
      exact (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right he (homogeneousFreeTestBound_nonneg a b φ))
        (norm_nonneg _)).trans_eq (mul_comm _ _))
    (hu.norm.const_mul _)
    (by
      filter_upwards [] with ξ t _
      exact (hasDerivAt_homogeneousFreeDualTest a b t φ ξ).const_mul (u ξ))
  have hf : (fun t : ℝ => homogeneousFourierPairing a k ha ha1 hk φ
      (homogeneousFreeOperator a b k t ha ha1 hk u)) =
      (fun t : ℝ => ∫ ξ : E, u ξ * homogeneousFreeDualTest a b t φ ξ) := by
    funext t
    exact homogeneousFreeOperator_fourier_duality a b k t ha ha1 hk φ u
  rw [hf]
  exact hd.2

theorem homogeneousFree_weak_generator (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u v : HomogeneousY a k)
    (hu : HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk u)
      v (Ici 0) 0) (φ : 𝓢(E, ℂ)) :
    homogeneousFourierPairing a k ha ha1 hk φ v =
      ∫ ξ : E, u ξ *
        (((-(a : ℂ) + Complex.I * (b : ℂ)) - Complex.I * (‖ξ‖ ^ 2 : ℝ)) * φ ξ -
          (1 / 2 : ℝ) • fderiv ℝ φ ξ ξ) := by
  let L := (homogeneousFourierPairing a k ha ha1 hk φ).restrictScalars ℝ
  have h₁ := L.hasFDerivAt.comp_hasDerivWithinAt 0 hu
  have h₂ := (hasDerivAt_homogeneousFourierPairing_free a b k ha ha1 hk u φ).hasDerivWithinAt
    (s := Ici 0)
  have he := (h₁.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (h₂.derivWithin (uniqueDiffWithinAt_Ici 0))
  simpa only [L, ContinuousLinearMap.coe_restrictScalars', Function.comp_def,
    homogeneousFreeDualDerivative, neg_zero, zero_div, Real.exp_zero, one_smul,
    homogeneousPhysicalAmplitude, mul_zero, Complex.ofReal_zero, zero_add,
    Complex.exp_zero, homogeneousSchrodingerPhase, sub_self, zero_mul, one_mul] using he

end DefocusingNLS

end OAI
