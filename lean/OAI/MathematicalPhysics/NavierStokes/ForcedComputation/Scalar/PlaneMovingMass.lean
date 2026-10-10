import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneMovingTest
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneIntegralBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMassCutoff

namespace OAI

/-! A moving compact test loses at most the diffusion budget. Transport
cancellation is an identity of the concrete test and velocity, while scalar
positivity and total mass are supplied by the preceding PDE lemmas. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian ExpandingDetector Set MeasureTheory
open scoped ContDiff

theorem PlaneScalarSolution.moving_mass_derivative_lower
    {T ν M L : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hν : 0 ≤ ν) (hL : 0 ≤ L)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    {φ φd : ℝ → Plane → ℝ}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (hφd : ContDiff ℝ ∞ (Function.uncurry φd))
    (hdφ : ∀ t x, HasDerivAt (fun s => φ s x) (φd t x) t)
    {K : Set Plane} (hK : IsCompact K)
    (hsupp : ∀ t, Function.support (φ t) ⊆ K)
    (hdsupp : ∀ t, Function.support (φd t) ⊆ K)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hwi : Integrable (w t)) (hwn : ∀ x, 0 ≤ w t x) (hwm : (∫ x, w t x) ≤ M)
    (hφn : ∀ x, 0 ≤ φ t x) (hhn : ∀ x, 0 ≤ h t x)
    (hΔ : ∀ x, |scalarLaplacian (φ t) x| ≤ L)
    (hcancel : ∀ x, φd t x + fderiv ℝ (φ t) x (a t x) = 0) :
    ∃ d : ℝ, HasDerivAt (fun r => ∫ x, φ r x * w r x) d t ∧ - (ν * L * M) ≤ d := by
  have hD := hw.moving_test_derivative ha hh hdiv hφ hφd hdφ hK hsupp hdsupp ht
  refine ⟨_, hD, ?_⟩
  have hφs : ContDiff ℝ ∞ (φ t) := hφ.comp (contDiff_const.prodMk contDiff_id)
  have hφds : ContDiff ℝ ∞ (φd t) := hφd.comp (contDiff_const.prodMk contDiff_id)
  have hwS := hw.slice_smooth (Ioo_subset_Icc_self ht)
  have haS : ContDiff ℝ ∞ (a t) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (φ t) := HasCompactSupport.intro (K := K) hK (fun x hx => by
    by_contra hn
    exact hx (hsupp t hn))
  have hdc : HasCompactSupport (φd t) := HasCompactSupport.intro (K := K) hK (fun x hx => by
    by_contra hn
    exact hx (hdsupp t hn))
  have hid : Integrable (fun x => φd t x * w t x) :=
    (hφds.mul hwS).continuous.integrable_of_hasCompactSupport hdc.mul_right
  have hgrad : HasCompactSupport (fun x => fderiv ℝ (φ t) x (a t x)) := by
    apply hc.mono'
    intro x hx
    by_contra hn
    exact hx (by simp [fderiv_of_notMem_tsupport ℝ hn])
  have hgc : HasCompactSupport (fun x => ν * scalarLaplacian (φ t) x +
      fderiv ℝ (φ t) x (a t x)) :=
    ((scalarLaplacian_compactSupport hc).mul_left).add hgrad
  have hig : Integrable (fun x => w t x * (ν * scalarLaplacian (φ t) x +
      fderiv ℝ (φ t) x (a t x))) :=
    (hwS.mul ((contDiff_const.mul (scalarLaplacian_smooth hφs)).add
      ((hφs.fderiv_right (m := ∞) (by simp)).clm_apply haS))).continuous.integrable_of_hasCompactSupport hgc.mul_left
  have he (x : Plane) : φd t x * w t x + w t x *
      (ν * scalarLaplacian (φ t) x + fderiv ℝ (φ t) x (a t x)) =
      ν * (w t x * scalarLaplacian (φ t) x) := by
    linear_combination (w t x) * hcancel x
  have hi : (∫ x, φd t x * w t x) +
      (∫ x, w t x * (ν * scalarLaplacian (φ t) x + fderiv ℝ (φ t) x (a t x))) =
      ν * ∫ x, w t x * scalarLaplacian (φ t) x := by
    rw [← integral_add hid hig]
    simp_rw [he]
    exact integral_const_mul _ _
  rw [hi]
  have hb := abs_integral_mul_le hwi (scalarLaplacian_smooth hφs).continuous.aestronglyMeasurable hΔ
  have habs : (∫ x, |w t x|) = ∫ x, w t x := by
    congr 1
    funext x
    exact abs_of_nonneg (hwn x)
  rw [habs] at hb
  have hlower : -(L * M) ≤ ∫ x, w t x * scalarLaplacian (φ t) x := by
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hwm hL)
    exact (abs_le.mp hb').1
  have hm := mul_le_mul_of_nonneg_left hlower hν
  have hhpos : 0 ≤ ∫ x, φ t x * h t x := integral_nonneg (fun x => mul_nonneg (hφn x) (hhn x))
  nlinarith

end ForcedComputation.VelocityDetector

end

end OAI
