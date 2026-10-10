import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTensorPullback
import OAI.Geometry.Immersion.ClosedSurface.MetricPullback

namespace OAI

noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.PhaseMean
open SmallModes

lemma evaluate_pullback (L : Base →L[ℝ] Base) (H : Tensor) (v w : Base) :
    evaluate (pullback L H) v w = evaluate H (L v) (L w) := by
  have hL (u : Base) : L u = u.1 • L dx + u.2 • L dy := by
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext <;> simp [dx,dy]
  change evaluate H (L dx) (L dx) * v.1 * w.1 +
    evaluate H (L dx) (L dy) * (v.1*w.2+v.2*w.1) +
    evaluate H (L dy) (L dy) * v.2 * w.2 = evaluate H (L v) (L w)
  rw [hL v,hL w]
  simp only [evaluate,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma positive_pullback (L : Base →L[ℝ] Base) (hL : Function.Injective L) {H : Tensor}
    (hH : 0 < H 0 ∧ 0 < H 0*H 2-(H 1)^2) :
    0 < pullback L H 0 ∧ 0 < pullback L H 0*pullback L H 2-(pullback L H 1)^2 := by
  apply (tensor_positive_iff _).mp
  intro v hv
  rw [evaluate_pullback]
  apply (tensor_positive_iff H).mpr hH
  intro hz
  exact hv (hL (by simpa using hz))

end ClosedSurfaceR4.PhaseMean

end

end OAI
