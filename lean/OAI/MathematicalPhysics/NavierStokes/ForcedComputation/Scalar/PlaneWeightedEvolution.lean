import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTestIntegral
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCompactTransport
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneInteriorCalculus

namespace OAI

/-! The whole-plane scalar equation tested against a compact smooth
function. Its spatial tails require no integration-by-parts boundary term. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff

theorem PlaneScalarSolution.test_integral_continuousOn
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ContinuousOn (fun r => ∫ x, φ x * w r x) (Icc 0 T) := by
  apply compact_supported_integral_continuousOn (g := fun p : ℝ × Plane => φ p.2 * w p.1 p.2)
    (((hφ.comp contDiff_snd).contDiffOn.mul hw.smooth).continuousOn) hc.isCompact
  intro r x hx
  by_contra hn
  apply hx
  change φ x * w r x = 0
  rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]

theorem PlaneScalarSolution.test_integral_derivative
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h))
    (hdiv : ∀ t x, divergence (a t) x = 0)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => ∫ x, φ x * w r x)
      ((∫ x, w t x * (ν * scalarLaplacian φ x + fderiv ℝ φ x (a t x))) +
        ∫ x, φ x * h t x) t := by
  let A : ℝ := t / 2
  let B : ℝ := (t + T) / 2
  have hi : Icc A B ⊆ Ioo (0 : ℝ) T := by
    intro s hs
    dsimp [A, B] at hs
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  have htAB : t ∈ Ioo A B := by constructor <;> dsimp [A, B] <;> linarith [ht.1, ht.2]
  have hp : ContDiff ℝ ∞ (fun p : ℝ × Plane => φ p.2) := hφ.comp contDiff_snd
  have hg : ContinuousOn (fun p : ℝ × Plane => φ p.2 * w p.1 p.2)
      (Icc A B ×ˢ univ) :=
    (hp.contDiffOn.mul (hw.smooth.mono (fun _ hs =>
      ⟨Ioo_subset_Icc_self (hi hs.1), hs.2⟩))).continuousOn
  have hd : ContinuousOn (fun p : ℝ × Plane => φ p.2 *
      (scalarGenerator ν (a p.1) (w p.1) p.2 + h p.1 p.2)) (Icc A B ×ˢ univ) :=
    (hp.contDiffOn.mul (((hw.interior_generator ha).add hh.contDiffOn).mono
      (fun _ hs => ⟨hi hs.1, hs.2⟩))).continuousOn
  have he (s : ℝ) (hs : s ∈ Ioo A B) (x : Plane) :
      HasDerivAt (fun r => φ x * w r x)
        (φ x * (scalarGenerator ν (a s) (w s) x + h s x)) s := by
    have hsT := hi (Ioo_subset_Icc_self hs)
    exact ((hw.equation s (Ioo_subset_Icc_self hsT) x).hasDerivAt
      (Icc_mem_nhds hsT.1 hsT.2)).const_mul (φ x)
  have hsupp (r : ℝ) : Function.support (fun x => φ x * w r x) ⊆ tsupport φ := by
    intro x hx
    by_contra hn
    apply hx
    change φ x * w r x = 0
    rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]
  have hdsupp : Function.support (fun x => φ x *
      (scalarGenerator ν (a t) (w t) x + h t x)) ⊆ tsupport φ := by
    intro x hx
    by_contra hn
    apply hx
    change φ x * (scalarGenerator ν (a t) (w t) x + h t x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]
  have hD := compact_supported_integral_hasDerivAt hg hd he hc.isCompact hsupp hdsupp htAB
  have hwS := hw.slice_smooth (Ioo_subset_Icc_self ht)
  have haS : ContDiff ℝ ∞ (a t) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hhS : ContDiff ℝ ∞ (h t) := hh.comp (contDiff_const.prodMk contDiff_id)
  have hG : ContDiff ℝ ∞ (scalarGenerator ν (a t) (w t)) := by
    apply ContDiff.sub
    · apply ContDiff.mul contDiff_const
      unfold scalarLaplacian
      exact ContDiff.sum (fun j _ => spatialD_smooth j (spatialD_smooth j hwS))
    · exact (hwS.fderiv_right (m := ∞) (by simp)).clm_apply haS
  have hig : Integrable (fun x => φ x * scalarGenerator ν (a t) (w t) x) :=
    (hφ.mul hG).continuous.integrable_of_hasCompactSupport hc.mul_right
  have hih : Integrable (fun x => φ x * h t x) :=
    (hφ.mul hhS).continuous.integrable_of_hasCompactSupport hc.mul_right
  have hI : (∫ x, φ x * (scalarGenerator ν (a t) (w t) x + h t x)) =
      (∫ x, w t x * (ν * scalarLaplacian φ x + fderiv ℝ φ x (a t x))) +
        ∫ x, φ x * h t x := by
    simp_rw [mul_add]
    rw [integral_add hig hih, integral_compact_generator hφ hwS haS hc (hdiv t) ν]
    simp only [mul_add]
  exact hI ▸ hD

end ForcedComputation.VelocityDetector

end

end OAI
