import Mathlib

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

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_linearization {Φ : P → F} {f : F → F} {U : Set P} {p a b : P}
    (hU : IsOpen U) (hp : p ∈ U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hf : DifferentiableAt ℝ f (Φ p))
    (hode : ∀ q ∈ U, fderiv ℝ Φ q a = f (Φ q)) :
    fderiv ℝ (fderiv ℝ Φ) p a b = fderiv ℝ f (Φ p) (fderiv ℝ Φ p b) := by
  have hc := (hΦ p hp).contDiffAt (hU.mem_nhds hp)
  have hdΦ := hc.differentiableAt (by norm_num)
  have hdD : DifferentiableAt ℝ (fderiv ℝ Φ) p :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := hdD.hasFDerivAt.clm_apply (hasFDerivAt_const a p)
  have hB := hf.hasFDerivAt.comp p hdΦ.hasFDerivAt
  have he : (fun q => fderiv ℝ Φ q a) =ᶠ[𝓝 p] (fun q => f (Φ q)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hode q hq
  have hlin := congrArg (fun L : P →L[ℝ] F => L b) (hA.unique (hB.congr_of_eventuallyEq he))
  have hs := hc.isSymmSndFDerivAt (by simp) a b
  simpa [hs] using hlin

theorem hasDerivAt_time_slice {Φ : ℝ × P → F} {t : ℝ} {x : P}
    (hΦ : DifferentiableAt ℝ Φ (t, x)) :
    HasDerivAt (fun r => Φ (r, x)) (fderiv ℝ Φ (t, x) (1, 0)) t := by
  have hd := hΦ.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  convert! hd using 1

theorem variation_hasDerivAt {Φ : ℝ × P → F} {f : F → F} {U : Set (ℝ × P)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hode : ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1)
    {T : ℝ} {x w : P} (hTx : (T, x) ∈ U) (hf : DifferentiableAt ℝ f (Φ (T, x))) :
    HasDerivAt (fun t => fderiv ℝ Φ (t, x) (0, w))
      (fderiv ℝ f (Φ (T, x)) (fderiv ℝ Φ (T, x) (0, w))) T := by
  have hc := (hΦ (T, x) hTx).contDiffAt (hU.mem_nhds hTx)
  have hdD : DifferentiableAt ℝ (fderiv ℝ Φ) (T, x) :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have htD := hasDerivAt_time_slice hdD
  have hd := (htD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, w) T)).hasDerivAt
  have he := directional_linearization hU hTx hΦ hf (a := (1, 0)) (b := (0, w)) (by
    intro q hq
    exact (hasDerivAt_time_slice (((hΦ q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by norm_num))).unique (hode q hq))
  convert! hd using 1
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, map_zero, zero_add]
  exact he.symm

end VariationCalculus

end

end WeakMTWGlobalSupport

end OAI
