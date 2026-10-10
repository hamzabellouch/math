import OAI.Geometry.RCD.Metric.BoundaryExteriorBall
import OAI.Geometry.RCD.Sobolev.ZeroFractionCoercivity
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # A boundary-layer estimate for the actual Dirichlet difference

Metric approximation furnishes an exterior ball at each shell point.
The proved volume comparison makes its relative mass uniform, and the
zero-fraction Poincare inequality gives the squared boundary scale.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.boundary_dirichlet_local {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {κ : ℝ} (hκ : 0≤κ) :
    ∃ C : ℝ, 0<C ∧ ∀ (p x : X) (r S R δ ε : ℝ),
      0<r → 0<δ → 4*δ≤R → R+2*δ≤S → 0≤ε → ε≤δ/8 →
      ∀ V : X → Euclidean n, IsPointedApproximation p 0 r S ε V →
      (R-δ)*r≤dist x p → dist x p≤R*r → -κ≤K*(5*δ*r)^2 →
      ∀ w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p (R*r)),
      (∫ z in ball x (5*δ*r), (SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val z)^2
        ∂hausdorff n X)≤C*δ^2*r^2*(∫ z in ball x (40*δ*r),
          localGamma (hausdorff n X) hX.quadratic w.val w.val z ∂hausdorff n X) := by
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn hκ
    (by norm_num : (0:ℝ)<1/20) (by norm_num : (1/20:ℝ)≤1)
  obtain ⟨C,hC,hP⟩ := hX.local_zero_fraction_coercivity hn hκ (by linarith : 0≤D)
  refine ⟨25*C,by positivity,?_⟩
  intro p x r S R δ ε hr hδ hR hS hε hεδ V hV hx₀ hx₁ hcurv w
  obtain ⟨y,_,_,hxy,hsub⟩ := pointed_boundary_exterior_ball hr hδ hR hS hε hεδ V hV hx₀ hx₁
  have hscale : 0<5*δ*r := by positivity
  have hxy' : dist y x≤5*δ*r := by rw [dist_comm]; nlinarith [mul_pos hδ hr]
  have hm := hvol x (5*δ*r) hscale hcurv y hxy'
  have he : (1/20:ℝ)*(5*δ*r)=δ/4*r := by ring
  rw [he] at hm
  have hz := SobolevSpace.dirichlet_zero_off (hausdorff n X) hX.quadratic
    (ball p (R*r)) measurableSet_ball w
  have hzB : SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val
      =ᵐ[(hausdorff n X).restrict (ball y (δ/4*r))] 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun _ ht => (hsub ht).2) hz
  have hh := hP x (5*δ*r) hscale hcurv w.val (ball y (δ/4*r))
    (fun _ ht => (hsub ht).1) hm hzB
  have he₈ : 8*(5*δ*r)=40*δ*r := by ring
  have he₂ : C*(5*δ*r)^2=(25*C)*δ^2*r^2 := by ring
  rwa [he₈,he₂] at hh

end RegularPointCoordinates

end

end OAI
