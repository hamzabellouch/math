import OAI.Analysis.CircleDomains.Modulus.DiskLinePayment
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-!
# The planar gradient density used in line payment

The two Euclidean components are the real derivative on `1` and `I`.
The horizontal line derivative is the first component, and the square
of the density is the ordinary Euclidean Dirichlet energy integrand.
-/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def horizontalLine (y : ℝ) (x : ℝ) : ℂ := ⟨x, y⟩

theorem continuous_horizontalLine (y : ℝ) : Continuous (horizontalLine y) :=
  Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)

theorem contDiff_horizontalLine (y : ℝ) : ContDiff ℝ 1 (horizontalLine y) :=
  Complex.equivRealProdCLM.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)

theorem hasDerivAt_horizontalLine (x y : ℝ) : HasDerivAt (horizontalLine y) 1 x := by
  exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

def euclideanGradientEnergy (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  (fderiv ℝ v z 1) ^ 2 + (fderiv ℝ v z Complex.I) ^ 2

def euclideanGradientNorm (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.sqrt (euclideanGradientEnergy v z)

theorem euclideanGradientEnergy_nonneg (v : ℂ → ℝ) (z : ℂ) :
    0 ≤ euclideanGradientEnergy v z := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem euclideanGradientNorm_sq (v : ℂ → ℝ) (z : ℂ) :
    euclideanGradientNorm v z ^ 2 = euclideanGradientEnergy v z :=
  Real.sq_sqrt (euclideanGradientEnergy_nonneg v z)

theorem measurable_euclideanGradientNorm (v : ℂ → ℝ) : Measurable (euclideanGradientNorm v) :=
  (((measurable_fderiv_apply_const ℝ v 1).pow_const 2).add
    ((measurable_fderiv_apply_const ℝ v Complex.I).pow_const 2)).sqrt

theorem memLp_indicator_euclideanGradientNorm {v : ℂ → ℝ} {E : Set ℂ}
    (hE : MeasurableSet E) (henergy : IntegrableOn (euclideanGradientEnergy v) E) :
    MemLp (E.indicator (euclideanGradientNorm v)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_euclideanGradientNorm v).indicator hE).aestronglyMeasurable).mpr
  convert henergy.integrable_indicator hE using 1
  funext z
  by_cases hz : z ∈ E
  · simp only [indicator_of_mem hz, euclideanGradientNorm_sq]
  · simp only [indicator_of_notMem hz, zero_pow (by norm_num : 2 ≠ 0)]

theorem horizontal_derivative_le_gradient {v : ℂ → ℝ} {x y : ℝ}
    (hv : DifferentiableAt ℝ v (horizontalLine y x)) :
    |deriv (v ∘ horizontalLine y) x| ≤ euclideanGradientNorm v (horizontalLine y x) := by
  rw [(hv.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_horizontalLine x y)).deriv]
  apply Real.le_sqrt_of_sq_le
  simp only [sq_abs, euclideanGradientEnergy]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem horizontal_cluster_is_planar {U : Set ℂ} {v : ℂ → ℝ} {x y t : ℝ}
    (h : MapClusterPt t (𝓝[horizontalLine y ⁻¹' U] x) (v ∘ horizontalLine y)) :
    MapClusterPt t (𝓝[U] (horizontalLine y x)) v := by
  apply MapClusterPt.of_comp _ h
  exact tendsto_nhdsWithin_iff.mpr
    ⟨(continuous_horizontalLine y).continuousAt.mono_left nhdsWithin_le_nhds,
      self_mem_nhdsWithin⟩

end CircleDomainRigidity

end

end OAI
