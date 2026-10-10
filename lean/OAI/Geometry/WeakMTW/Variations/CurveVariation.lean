import Mathlib
import OAI.Geometry.WeakMTW.Variations.CurveCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace VariationCalculus
open Set Filter
open scoped Topology ContDiff
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem parameter_variation_hasDerivAt {Φ Ψ : ℝ × P → F} {U : Set (ℝ × P)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (htime : ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (Ψ q) q.1)
    {T : ℝ} {x w : P} (hTx : (T, x) ∈ U)
    (hΨ : DifferentiableAt ℝ Ψ (T, x)) :
    HasDerivAt (fun t => fderiv ℝ Φ (t, x) (0, w))
      (fderiv ℝ Ψ (T, x) (0, w)) T := by
  have hc := (hΦ (T, x) hTx).contDiffAt (hU.mem_nhds hTx)
  have hdD : DifferentiableAt ℝ (fderiv ℝ Φ) (T, x) :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := hdD.hasFDerivAt.clm_apply (hasFDerivAt_const (1, 0) (T, x))
  have heq : (fun q => fderiv ℝ Φ q (1, 0)) =ᶠ[𝓝 (T, x)] Ψ := by
    filter_upwards [hU.mem_nhds hTx] with q hq
    exact (hasDerivAt_time_slice (((hΦ q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by norm_num))).unique (htime q hq)
  have he := congrArg (fun L : (ℝ × P) →L[ℝ] F => L (0, w))
    (hA.unique (hΨ.hasFDerivAt.congr_of_eventuallyEq heq))
  have hs := hc.isSymmSndFDerivAt (by simp) (1, 0) (0, w)
  have hd := ((hasDerivAt_time_slice hdD).hasFDerivAt.clm_apply (hasFDerivAt_const (0, w) T)).hasDerivAt
  convert! hd using 1
  simpa [hs] using he.symm

end VariationCalculus

end

end WeakMTWGlobalSupport

end OAI
