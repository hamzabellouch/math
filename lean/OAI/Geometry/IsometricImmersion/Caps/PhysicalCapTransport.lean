import OAI.Geometry.IsometricImmersion.Caps.ConstructedCapGradient
import OAI.Geometry.IsometricImmersion.Caps.UniformOriginalDataCapEstimate

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightCapIntegralFactors (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : ℝ × ℝ :=
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
  let M := heightCapCoefficientBound G Z d c e0 ell
  let MK := heightCapCurvatureBound G Z d c
  let glow := heightG1Lower G Z d c e0
  let MI := 2*heightBJetBound G Z d c ell
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  let S := 2/(c2*capInteriorWeightFloor top b lambda MI)
  (S*((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6),
    S*(COverlap*(D^6+HElliptic)))

def heightPhysicalCapConstant (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : ℝ :=
  let H := Real.exp (2*heightQuotientJetBound G Z d c)
  let A := heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b
  H*(2+3*H^2)*H*(|A.1|+|A.2|+1)

theorem heightPhysicalCapConstant_pos (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : 0 < heightPhysicalCapConstant G Z d c e0 kappa ell L R bottom top b := by
  unfold heightPhysicalCapConstant
  positivity

theorem heightUniformCapEstimateRHS_eq_factors (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) (u f : Coord → ℝ) :
    heightUniformCapEstimateRHS G Z d c e0 kappa ell L R bottom top b u f =
      (heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b).1*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)+
      (heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b).2*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2) := by
  unfold heightUniformCapEstimateRHS heightCapIntegralFactors
  ring

theorem scalar_two_integral_transport
    {a b H J F U Fp Up P Q : ℝ} (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hF : 0 ≤ F) (hU : 0 ≤ U) (hFp : 0 ≤ Fp) (hUp : 0 ≤ Up)
    (hFle : F ≤ H*Fp) (hUle : U ≤ H*Up)
    (hP : P ≤ a*F+b*U) (hQ : Q ≤ J*P) :
    Q ≤ J*H*(|a|+|b|+1)*(Fp+Up) := by
  have habs : a*F+b*U ≤ |a| *F+|b| *U :=
    add_le_add (mul_le_mul_of_nonneg_right (le_abs_self a) hF)
      (mul_le_mul_of_nonneg_right (le_abs_self b) hU)
  have harea : |a| *F+|b| *U ≤ H*(|a| *Fp+|b| *Up) := by
    calc
      _ ≤ |a| *(H*Fp)+|b| *(H*Up) :=
        add_le_add (mul_le_mul_of_nonneg_left hFle (abs_nonneg a))
          (mul_le_mul_of_nonneg_left hUle (abs_nonneg b))
      _ = _ := by ring
  have hsum : |a| *Fp+|b| *Up ≤ (|a|+|b|+1)*(Fp+Up) := by
    have h1 := mul_nonneg (abs_nonneg a) hUp
    have h2 := mul_nonneg (abs_nonneg b) hFp
    nlinarith only [h1,h2,hFp,hUp]
  calc
    Q ≤ J*P := hQ
    _ ≤ J*(a*F+b*U) := mul_le_mul_of_nonneg_left hP hJ
    _ ≤ J*(|a| *F+|b| *U) := mul_le_mul_of_nonneg_left habs hJ
    _ ≤ J*(H*(|a| *Fp+|b| *Up)) := mul_le_mul_of_nonneg_left harea hJ
    _ ≤ J*(H*((|a|+|b|+1)*(Fp+Up))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hH) hJ
    _ = _ := by ring

theorem cap_gradient_estimate_to_physical_images
    {Y : ℝ → ℝ → ℝ} {q u f : Coord → ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2:ℝ) 2) t)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    (hu : ContDiffOn ℝ ∞ u V) (hV : IsOpen V)
    (hmap : MapsTo (capChart Y) capChartDomain V)
    {tl tr sb st TL TR SB ST M a b : ℝ}
    (ht : tl ≤ tr) (hs : sb ≤ st) (hT : TL ≤ TR) (hS : SB ≤ ST)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hBOX : closedRectangle TL TR SB ST ⊆ capChartDomain)
    (hq : ∀ p ∈ capChartDomain, |q (capChart Y p)| ≤ 1)
    (hJ : ∀ p ∈ capChartDomain,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    (hf : ContinuousOn f (capChart Y '' closedRectangle TL TR SB ST))
    (hestimate : rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y u)) ≤
      a*rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2)+
        b*rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2)) :
    (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare u p) ≤
      (Real.exp (2*M)*(2+3*(Real.exp (2*M))^2))*Real.exp (2*M)*(|a|+|b|+1)*
        ((∫ p in capChart Y '' closedRectangle TL TR SB ST, (f p)^2)+
          (∫ p in capChart Y '' closedRectangle TL TR SB ST, (u p)^2)) := by
  have huI : ContinuousOn u (capChart Y '' closedRectangle TL TR SB ST) :=
    hu.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmap (hBOX hp))
  have hfc : ContinuousOn (capPullback Y f) (closedRectangle TL TR SB ST) :=
    hf.comp ((capChart_contDiffOn hYs).continuousOn.mono hBOX) (fun p hp => ⟨p,hp,rfl⟩)
  have huc : ContinuousOn (capPullback Y u) (closedRectangle TL TR SB ST) :=
    (capPullback_contDiffOn hYs hu hmap).continuousOn.mono hBOX
  have hF : 0 ≤ rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2) := by
    have he := rectangleIntegral_eq_coordinate_closed_area hT hS (hfc.pow 2)
    change rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2) = _ at he
    rw [he]
    exact integral_nonneg (fun p => sq_nonneg _)
  have hU : 0 ≤ rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2) := by
    have he := rectangleIntegral_eq_coordinate_closed_area hT hS (huc.pow 2)
    change rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2) = _ at he
    rw [he]
    exact integral_nonneg (fun p => sq_nonneg _)
  have hFarea := cap_pullback_square_integral_le_image hYs hvar hsource heq hT hS hBOX
    (fun p hp => hJ p (hBOX hp)) hf
  have hUarea := cap_pullback_square_integral_le_image hYs hvar hsource heq hT hS hBOX
    (fun p hp => hJ p (hBOX hp)) huI
  have hGrad := (cap_gradient_integral_bounds hYs hvar hode hsource heq hu hV hmap ht hs hbox
    (fun p hp => hq p (hbox hp)) (fun p hp => hJ p (hbox hp))).2
  exact scalar_two_integral_transport (Real.exp_pos _).le (by positivity) hF hU
    (integral_nonneg (fun p => sq_nonneg (f p))) (integral_nonneg (fun p => sq_nonneg (u p)))
    hFarea hUarea hestimate hGrad

end SmoothLocal.Flow

end

end OAI
