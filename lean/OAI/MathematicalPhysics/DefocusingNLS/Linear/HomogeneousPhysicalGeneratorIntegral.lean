import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalKernelDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakGenerator

namespace OAI

/-! # A physical integral formula for the strong free generator

The derivative comes from the actual Fourier representation of the free
flow. In particular it applies to the generator vectors selected by the
finite spectral contour, with no additional spatial regularity hypothesis.
-/

open Set Filter MeasureTheory Topology
open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem continuous_physicalFreeKernel (a b t : ℝ) (y : E) :
    Continuous (fun ξ : E => homogeneousPhysicalFreeKernel a b t y ξ) := by
  unfold homogeneousPhysicalFreeKernel
  fun_prop

private theorem continuous_physicalFreeKernelDerivative (a b t : ℝ) (y : E) :
    Continuous (fun ξ : E => homogeneousPhysicalFreeKernelDerivative a b t y ξ) := by
  have hK := continuous_physicalFreeKernel a b t y
  unfold homogeneousPhysicalFreeKernelDerivative
  apply hK.mul
  fun_prop

theorem hasDerivAt_homogeneousFree_physical (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (y : E) :
    HasDerivAt (fun t : ℝ => homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousFreeOperator a b k t ha ha1 hk u) y)
      ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) *
        ∫ ξ : E, homogeneousPhysicalFreeKernelDerivative a b 0 y ξ * u ξ) 0 := by
  have hu := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)).1
  have h₂ := integrable_homogeneousFourier_secondMoment a k ha ha1 hk u
  let C := Real.exp a * (‖-(a : ℂ) + Complex.I * (b : ℂ)‖ + Real.exp 1 * (1 + ‖y‖))
  have hbound : Integrable (fun ξ : E => C * (1 + ‖ξ‖ ^ 2) * ‖u ξ‖) := by
    convert (hu.norm.add h₂).const_mul C using 1
    funext ξ
    dsimp only [Pi.add_apply]
    ring
  have hzero : Integrable (fun ξ : E => homogeneousPhysicalFreeKernel a b 0 y ξ * u ξ) := by
    apply hu.norm.mono' ((continuous_physicalFreeKernel a b 0 y).aestronglyMeasurable.mul
      hu.aestronglyMeasurable)
    filter_upwards [] with ξ
    dsimp only [Pi.mul_apply]
    rw [norm_mul, homogeneousPhysicalFreeKernel_norm]
    simp
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (x₀ := (0 : ℝ)) (s := Ioo (-1 : ℝ) 1)
    (F := fun t ξ => homogeneousPhysicalFreeKernel a b t y ξ * u ξ)
    (F' := fun t ξ => homogeneousPhysicalFreeKernelDerivative a b t y ξ * u ξ)
    (bound := fun ξ => C * (1 + ‖ξ‖ ^ 2) * ‖u ξ‖)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (continuous_physicalFreeKernel a b t y).aestronglyMeasurable.mul
      hu.aestronglyMeasurable)
    hzero
    ((continuous_physicalFreeKernelDerivative a b 0 y).aestronglyMeasurable.mul hu.aestronglyMeasurable)
    (by
      filter_upwards [] with ξ t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (homogeneousPhysicalFreeKernelDerivative_local_bound a b t ha ht y ξ) (norm_nonneg _))
    hbound
    (by
      filter_upwards [] with ξ t _
      exact (hasDerivAt_homogeneousPhysicalFreeKernel a b t y ξ).mul_const (u ξ))
  have he : (fun t : ℝ => homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousFreeOperator a b k t ha ha1 hk u) y) =
      (fun t : ℝ => (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) *
        ∫ ξ : E, homogeneousPhysicalFreeKernel a b t y ξ * u ξ) := by
    funext t
    simpa only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_ofNat] using homogeneousFreeOperator_physical_integral a b k t ha ha1 hk u y
  rw [he]
  exact hd.2.const_mul _

theorem homogeneousFree_generator_physical_integral (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u v : HomogeneousY a k)
    (hu : HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk u)
      v (Ici 0) 0) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk v y =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) *
        ∫ ξ : E, homogeneousPhysicalFreeKernelDerivative a b 0 y ξ * u ξ := by
  let L := (homogeneousPointEvaluation a k ha ha1 hk y).restrictScalars ℝ
  have hL (f : HomogeneousY a k) : L f = homogeneousPhysicalCLM a k ha ha1 hk f y := rfl
  have h₁ := L.hasFDerivAt.comp_hasDerivWithinAt 0 hu
  have h₂ := (hasDerivAt_homogeneousFree_physical a b k ha ha1 hk u y).hasDerivWithinAt
    (s := Ici 0)
  have he := (h₁.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (h₂.derivWithin (uniqueDiffWithinAt_Ici 0))
  simpa only [hL, Function.comp_def] using he

end DefocusingNLS

end OAI
