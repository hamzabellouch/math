import OAI.Geometry.RCD.Transport.NearbySegmentCompression

namespace OAI

/-! # Controlled segments with endpoints near prescribed points

Only a dimensional constant and the explicit endpoint radius loss occur.
The estimate uses the original Hausdorff measure and permits every real K.
-/

open Set Filter Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

def segmentCost (n : ℕ) : ℝ := Real.exp (n:ℝ)*(Real.cosh 1^(n-1)*2^n)

theorem NoncollapsedRCD.nearby_defect_segment {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p x y : X} {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ ≤ R/2)
    (hx : dist x p ≤ R/2) (hy : dist y p ≤ R/2)
    (hcurv : -1 ≤ K*(4*R)^2)
    {F : X → ℝ} (hF : IntegrableOn F (ball p (8*R)) (hausdorff n X))
    (hFpos : ∀ᵐ z ∂(hausdorff n X).restrict (ball p (8*R)), 0 ≤ F z)
    {P : X → Prop} (hP : ∀ᵐ z ∂(hausdorff n X).restrict (ball p (8*R)), P z) :
    ∃ γ : C(Time,X), IsGeodesic γ ∧ dist (γ 0) x < ρ ∧ dist (γ 1) y < ρ ∧
      (∀ t : Time, dist (γ t) p ≤ 3*R) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), P (geodesicExtension γ t)) ∧
      |dist (γ 0) (γ 1)-dist x y| ≤ 2*ρ ∧
      IntegrableOn (fun t => F (geodesicExtension γ t)) (Icc (0:ℝ) 1) ∧
      (∫ t in Icc (0:ℝ) 1, F (geodesicExtension γ t)) ≤
        (segmentCost n*R^n/((hausdorff n X).real (ball p R)*ρ^n))*
          ∫ z in ball p (8*R), F z ∂hausdorff n X := by
  let K' := min K 0
  have hK' : K' ≤ 0 := min_le_right _ _
  have hY : NoncollapsedRCD K' n X := by
    by_cases hK : K ≤ 0
    · simpa only [K',min_eq_left hK] using hX
    · simpa only [K',min_eq_right (le_of_not_ge hK)] using
        hX.zero_of_nonneg_curvature hn (le_of_not_ge hK)
  have hc4 : -1 ≤ K'*(4*R)^2 := by
    by_cases hK : K ≤ 0
    · simpa only [K',min_eq_left hK] using hcurv
    · simp only [K',min_eq_right (le_of_not_ge hK),zero_mul]
      norm_num
  have hc2 : -1 ≤ K'*(2*R)^2 := by nlinarith
  have hsub (z : X) (hz : dist z p ≤ R/2) : ball z ρ ⊆ closedBall p R := by
    intro w hw
    have htri := dist_triangle w z p
    have hwz : dist w z < ρ := hw
    change dist w p ≤ R
    linarith
  obtain ⟨γ,hg,ha,hb,hstay,hPγ,hinner,hbound⟩ := hY.exists_defect_segment hn p hR
    measurableSet_ball measurableSet_ball (hY.fullSupport x ρ hρ).ne'
    (hY.fullSupport y ρ hρ).ne' (hsub x hx) (hsub y hy) hF hFpos hP
  have ha' : dist (γ 0) x < ρ := ha
  have hb' : dist (γ 1) y < ρ := hb
  refine ⟨γ,hg,ha',hb',hstay,hPγ,?_,hinner,?_⟩
  · apply abs_le.mpr
    have hupper := dist_triangle (γ 0) x y
    have hupper' := dist_triangle (γ 0) y (γ 1)
    have hlower := dist_triangle x (γ 0) (γ 1)
    have hlower' := dist_triangle x (γ 1) y
    rw [dist_comm y (γ 1)] at hupper'
    rw [dist_comm x (γ 0)] at hlower
    constructor <;> linarith
  · have hE := compressionBudget_le_of_rescaled_curvature hn hK' hc4
      (max ((hausdorff n X) (ball x ρ))⁻¹ ((hausdorff n X) (ball y ρ))⁻¹)
    have hC := hY.endpoint_ball_compression_bound (p:=p) (x:=x) (y:=y) hn hR hρ (by linarith) (by linarith)
      (by linarith) hc2
    have hcoeff := hE.trans (mul_le_mul_of_nonneg_left hC (Real.exp_pos (n:ℝ)).le)
    have hI : 0 ≤ ∫ z in ball p (8*R), F z ∂hausdorff n X := integral_nonneg_of_ae hFpos
    apply hbound.trans
    convert mul_le_mul_of_nonneg_right hcoeff hI using 1
    dsimp only [segmentCost]
    ring

end RegularPointCoordinates

end

end OAI
