import OAI.Geometry.RCD.Harmonic.FirstOrderSmallScaleApproximation
import OAI.Geometry.RCD.Metric.PointedPhysicalScale

namespace OAI

/-! # A fixed interior coordinate consequence on the original splitting scale -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_inner_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    {η : ℝ} (hη : 0<η) :
    ∃ r₀ ε : ℝ, 0<r₀ ∧ 0<ε ∧ ∀ (p : X) (r : ℝ), 0<r → r ≤ r₀ →
      -1≤K*(16*r)^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v →
        IsPointedApproximation p 0 r (1/2560) η (fun x => r⁻¹ • (v x-v p)) := by
  obtain ⟨s₀,ε,hs₀,hε,happly⟩ := hX.first_order_small_scale_approximation hn hK
    (show 0<5120*η by positivity)
  refine ⟨5120*s₀,ε,by positivity,hε,?_⟩
  intro p r hr hr₀ hc u v hs
  have he : 81920*(r/5120)=16*r := by ring
  have hh := happly p (r/5120) (by positivity) (by linarith)
    (by simpa only [he] using hc) u v (by simpa only [he] using hs)
  have hh' : IsPointedApproximation p 0 ((1/5120)*r) 2 (5120*η)
      (fun x => (r/5120)⁻¹ • (v x-v p)) := by
    simpa only [one_div_mul_eq_div] using hh
  have hout := hh'.change_scale hr (by norm_num : (0:ℝ)<1/5120)
  simpa only [show (1/5120:ℝ)*2=1/2560 by norm_num,
    show (1/5120:ℝ)*(5120*η)=η by ring,smul_smul,
    show (1/5120:ℝ)*(r/5120)⁻¹=r⁻¹ by field_simp] using hout

end RegularPointCoordinates

end

end OAI
