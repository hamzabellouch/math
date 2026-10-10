import Mathlib
import OAI.Geometry.BallPacking.Continuation.ProperPaths

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking
open Rigidity Rigidity.HolderCompletion

 theorem adapted_affine_line {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    (hinside : tsupport (fun x => J x-standardJ n)⊆openBall n 1)
    (p q : Phase n) (hpq : p≠q) : ∃ u,AffineLineCurve J p q u := by
  let : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
  let : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
  let : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
  let : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
  obtain ⟨β,β₁,M,δ,hpath,hend⟩ := adapted_line_continuation_data hJs hJ hJc hinside p q hpq
  let : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) β.rOut)) := inferInstance
  let : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) β.rOut)) := inferInstance
  let : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) β.rOut)) := inferInstance
  let : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) β.rOut)) := inferInstance
  obtain ⟨w,hw,hz⟩ := hpath.endpoint_exists
  exact ⟨_,hend w hw hz⟩

 theorem normalized_two_ball_bound (n : ℕ) (_ : 3≤n)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (hp : HasPacking n 2 1 ![a,b]) : a+b≤1 := by
  obtain ⟨J,p,q,hJs,hJ,hJc,hinside,hpq,harea⟩ := packing_two_line_reduction ha hb hp
  obtain ⟨u,hu⟩ := adapted_affine_line hJs hJ hJc hinside p q hpq
  exact harea u hu

end HigherDimensionalBallPacking

end

end OAI
