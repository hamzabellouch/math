import OAI.Geometry.IsometricImmersion.Caps.NestedCapRectangles
import OAI.Geometry.IsometricImmersion.Caps.AllOrderPhysicalCap

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

variable {bStar : ℝ}

structure CapInductionHeight (g : MetricField) (U : Set Coord) (Z c e0 : ℝ)
    (z : Coord → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ z U
  lowJet : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z
  denominator : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|
  energy : ∀ p ∈ modelSquare, e0 ≤ heightEnergy g z p
  quotient : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ)/100
  darboux : ∀ p ∈ modelSquare,
    (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p

def lowerCapConstant (G Z d c e0 kappa : ℝ) (ell : ℕ) (r : LowerCapRectangle bStar) : ℝ :=
  heightPhysicalCapConstant G Z d c e0 kappa ell r.left r.right r.bottom r.top ((r.top+bStar)/2)

theorem lowerCapConstant_pos (G Z d c e0 kappa : ℝ) (ell : ℕ) (r : LowerCapRectangle bStar) :
    0 < lowerCapConstant G Z d c e0 kappa ell r :=
  heightPhysicalCapConstant_pos G Z d c e0 kappa ell r.left r.right r.bottom r.top ((r.top+bStar)/2)

structure CapInductionFlow (g : MetricField) (U : Set Coord) (G Z d c e0 kappa : ℝ)
    (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord) : Prop where
  domainOpen : IsOpen W
  squareSubset : modelSquare ⊆ W
  domainSubset : W ⊆ U
  quotientSmooth : ContDiffOn ℝ ∞ (hessianQuotient g z) W
  quotientBound : CoordinateBound (hessianQuotient g z) modelSquare 3 (heightQuotientJetBound G Z d c)
  continuous : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2)
  jointSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)
  start : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s
  ode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
    HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t
  range : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3
  displacement : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50
  physicalEstimate : ∀ m : ℕ, ∀ {bStar : ℝ}, ∀ r : LowerCapRectangle bStar,
    (∫ p in r.image Y, (coordPartial 0 (verticalJet z (m+3)) p)^2+(verticalJet z (m+4) p)^2) ≤
      lowerCapConstant G Z d c e0 kappa (m+3) r *
        ((∫ p in r.energyOuter.image Y, (actualHighRemainder g z m p)^2)+
          (∫ p in r.energyOuter.image Y, (verticalJet z (m+3) p)^2))

theorem exists_capInductionFlow
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hh : CapInductionHeight (g0+eta) U Z c e0 z)
    (hk : 0 < kappa) (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (W : Set Coord) (Y : ℝ → ℝ → ℝ), CapInductionFlow (g0+eta) U G Z d c e0 kappa z Y W := by
  obtain ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hrange,hdisp50,hdisp,himages,hcap⟩ :=
    exists_C8_one_flow_physical_cap_estimates hg hU hSU hh.smooth hG hZ hd hc he0 hgB hh.lowJet
      hdet hh.denominator hh.energy hh.quotient hh.darboux hk hbackground hsupport hcentral
  refine ⟨V, Y, hV, hSV, hVU, hq, hqB, hY, hYs, hstart, hode, hrange, hdisp, ?_⟩
  intro m bStar r
  exact ((hcap m).2 r.left r.right r.bottom r.top ((r.top+bStar)/2) r.left_gt r.right_lt r.bottom_gt
    r.horizontal r.vertical (by linarith [r.top_lt]) (by linarith [r.top_lt,r.ceiling_le])).2

theorem CapInductionFlow.image_properties
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W) (r : LowerCapRectangle bStar) :
    IsCompact (r.image Y) ∧ MeasurableSet (r.image Y) ∧ volume (r.image Y) < ⊤ ∧
      r.image Y ⊆ modelOpenSquare :=
  cap_closed_image_properties hf.jointSmooth hf.displacement r.region_subset_domain

theorem CapInductionFlow.image_subset_square
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W) (r : LowerCapRectangle bStar) :
    r.image Y ⊆ modelSquare := (hf.image_properties r).2.2.2.trans modelOpenSquare_subset

theorem CapInductionFlow.pointwise_from_larger_L2
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (r : LowerCapRectangle bStar) {n : ℕ} {H : ℝ≥0}
    (hL : CoordinateL2Bound z (r.expand.image Y) (n+2) H) :
    CoordinateBound z (r.image Y) n
      ((squareSobolevWeight (flowInteriorRadius (heightQuotientJetBound G Z d c) r.margin r.margin)+1)*(H : ℝ)) := by
  apply coordinateL2Bound_to_expanded_cap_coordinateBound hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode (heightQuotientJetBound_nonneg hG hZ hd hc)
    hh.quotient (fun p hp => hf.quotientBound [1] (by norm_num) p hp)
    (hh.smooth.mono hf.domainSubset) r hL

def originalC8L2Budget (Z : ℝ) : ℝ≥0 :=
  (‖Z‖ₑ * (volume modelSquare) ^ (1/(2 : ℝ))).toNNReal

theorem originalC8L2Budget_coe (Z : ℝ) :
    (originalC8L2Budget Z : ℝ≥0∞) = ‖Z‖ₑ * (volume modelSquare) ^ (1/(2 : ℝ)) := by
  apply ENNReal.coe_toNNReal
  exact (ENNReal.mul_lt_top (by finiteness)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) modelSquare_isCompact.measure_lt_top.ne)).ne

theorem CapInductionHeight.original_L2
    {g : MetricField} {U : Set Coord} {Z c e0 : ℝ} {z : Coord → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hZ : 0 ≤ Z) {V : Set Coord} (hV : MeasurableSet V) (hVS : V ⊆ modelSquare) :
    CoordinateL2Bound z V 8 (originalC8L2Budget Z) := by
  have hC := coordinateBound_of_frechet_bounds hh.smooth hU hSU hh.lowJet
  intro ds hds
  rw [originalC8L2Budget_coe]
  exact (bounded_real_eLpNorm_two hV hZ (fun p hp => by
    rw [Real.norm_eq_abs]
    exact hC ds hds p (hVS hp))).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (z := 1/(2 : ℝ)) (measure_mono hVS) (by norm_num)))

theorem compact_continuous_memLp_two {f : Coord → ℝ} {V : Set Coord}
    (hV : IsCompact V) (hf : ContinuousOn f V) : MemLp f 2 (volume.restrict V) :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable hV.isClosed.measurableSet)).mpr
    ((hf.pow 2).integrableOn_compact hV)

theorem integral_each_sq_le_sum {f h : Coord → ℝ} {V : Set Coord}
    (hV : IsCompact V) (hf : ContinuousOn f V) (hh : ContinuousOn h V) :
    (∫ p in V, (f p)^2) ≤ ∫ p in V, (f p)^2+(h p)^2 ∧
      (∫ p in V, (h p)^2) ≤ ∫ p in V, (f p)^2+(h p)^2 := by
  have hfI : IntegrableOn (fun p => (f p)^2) V volume := (hf.pow 2).integrableOn_compact hV
  have hhI : IntegrableOn (fun p => (h p)^2) V volume := (hh.pow 2).integrableOn_compact hV
  exact ⟨setIntegral_mono_on hfI (hfI.add hhI) hV.isClosed.measurableSet
      (fun p hp => le_add_of_nonneg_right (sq_nonneg _)),
    setIntegral_mono_on hhI (hfI.add hhI) hV.isClosed.measurableSet
      (fun p hp => le_add_of_nonneg_left (sq_nonneg _))⟩

end SmoothLocal.Flow

end

end OAI
