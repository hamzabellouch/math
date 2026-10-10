import OAI.Geometry.Immersion.ClosedSurface.TensorBounds

namespace OAI

/-! Mixed metric bounds from the actual first derivatives of the two inputs. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates PhaseMean

lemma weighted_realLinearizedTensor_of_derivatives {n : ℕ} {U : Set Base}
    (hU : IsOpen U) {X Y : RField n} {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hbX : ∀ v : Base, ‖v‖ ≤ 1 → WeightedBound U s m C (coordDeriv v X))
    (hbY : ∀ v : Base, ‖v‖ ≤ 1 → WeightedBound U s m D (coordDeriv v Y)) :
    WeightedBound U s m (2*(n:ℝ)*(2^m*C*D)) (realLinearizedTensor X Y) := by
  have hdot (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :=
    (hbX v hv).dot_real hU.uniqueDiffOn hs.le hC hD
      (contDiffOn_coordDeriv_vector hU hX v) (contDiffOn_coordDeriv_vector hU hY w) (hbY w hw)
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
  · exact contDiffOn_pi.mp (contDiffOn_realLinearizedTensor hU hX hY)
  · intro i
    have hh := (hdot _ _ (norm_firstDirection i) (norm_secondDirection i)).add hU.uniqueDiffOn hs.le
      (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _) (contDiffOn_coordDeriv_vector hU hY _))
      (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _) (contDiffOn_coordDeriv_vector hU hY _))
      (hdot _ _ (norm_secondDirection i) (norm_firstDirection i))
    simp only [Fintype.card_fin] at hh
    have he : (n:ℝ)*(2^m*C*D)+(n:ℝ)*(2^m*C*D) = 2*(n:ℝ)*(2^m*C*D) := by ring
    rw [he] at hh
    simpa only [realLinearizedTensor_apply,realLinearized] using hh

end ClosedSurfaceR4.RealModes

end

end OAI
