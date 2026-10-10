import OAI.Geometry.RCD.Coordinates.CenteredFirstOrderFrame

namespace OAI

/-! # Bounds for the actual centered scalar coordinate functions -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.first_order_metric_bounds {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {p : X} {r ε : ℝ}
    (hr : 0<r) (hε : 0≤ε) (hε1 : ε≤1)
    {u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic} {v : X → Euclidean n}
    (hsplit : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (80*r) ε u v)
    (i : Fin n) :
    (∀ x, dist x p≤5*r → |(v x i-v p i)/r|≤10) ∧
    (∀ x y, dist x p≤5*r → dist y p≤5*r →
      |(v x i-v p i)/r-(v y i-v p i)/r|≤(2:ℝ≥0)*(dist x y/r)) := by
  have hg : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (80*r)),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x≤((2:ℝ≥0):ℝ)^2 := by
    filter_upwards [hsplit.gradient i] with x hx
    norm_num only [NNReal.coe_ofNat]
    nlinarith
  have hv : ContinuousOn (fun x => v x i) (ball p (8*(10*r))) := by
    have hh : ContinuousOn (fun x => v x i) (ball p (80*r)) :=
      (EuclideanSpace.proj i).continuous.comp_continuousOn hsplit.continuous
    simpa only [show (8:ℝ)*(10*r)=80*r by ring] using hh
  have hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i) =ᵐ[
      (hausdorff n X).restrict (ball p (8*(10*r)))] fun x => v x i := by
    simpa only [show (8:ℝ)*(10*r)=80*r by ring] using hsplit.representative i
  have hg' : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*(10*r))),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x≤((2:ℝ≥0):ℝ)^2 := by
    simpa only [show (8:ℝ)*(10*r)=80*r by ring] using hg
  have hl := hX.continuous_local_gradient_lipschitz hn (u i) (fun x => v x i) p
    (show 0<10*r by positivity) 2 hv hrep hg'
  have hin (x : X) (hx : dist x p≤5*r) : x∈ball p (10*r) := by
    change dist x p<10*r
    linarith
  have hpair (x y : X) (hx : dist x p≤5*r) (hy : dist y p≤5*r) :
      |v x i-v y i|≤2*dist x y := by
    simpa only [Real.dist_eq,NNReal.coe_ofNat] using hl.dist_le_mul x (hin x hx) y (hin y hy)
  constructor
  · intro x hx
    rw [abs_div,abs_of_pos hr]
    apply (div_le_iff₀ hr).mpr
    have hp : dist p p≤5*r := by simp; positivity
    nlinarith [hpair x p hx hp]
  · intro x y hx hy
    rw [← sub_div,sub_sub_sub_cancel_right,abs_div,abs_of_pos hr]
    change |v x i-v y i|/r≤2*(dist x y/r)
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (hpair x y hx hy) hr.le

end RegularPointCoordinates

end

end OAI
