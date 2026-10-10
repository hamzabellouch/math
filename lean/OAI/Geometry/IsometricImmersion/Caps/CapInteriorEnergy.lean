import OAI.Geometry.IsometricImmersion.Caps.IntegratedCapOverlap

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow

def capInteriorWeightFloor (top b lambda MI : ℝ) : ℝ :=
  (b-top)^8*Real.exp (-lambda*top-MI)

theorem capInteriorWeightFloor_pos {top b lambda MI : ℝ} (htop : top < b) :
    0 < capInteriorWeightFloor top b lambda MI :=
  mul_pos (pow_pos (sub_pos.mpr htop) _) (Real.exp_pos _)

theorem directedWeight_interior_lower {I : Coord → ℝ} {p : Coord} {top b lambda MI : ℝ}
    (htop : top < b) (hlambda : 0 ≤ lambda) (hp : p 1 ≤ top) (hI : |I p| ≤ MI) :
    capInteriorWeightFloor top b lambda MI ≤ directedWeight b lambda I p := by
  have hdist : b-top ≤ edgeDistance b p := by unfold edgeDistance; linarith
  have hpow := pow_le_pow_left₀ (sub_pos.mpr htop).le hdist 8
  have hphase : -lambda*top-MI ≤ weightPhase lambda I p := by
    have hm := mul_le_mul_of_nonneg_left hp hlambda
    unfold weightPhase
    linarith [(abs_le.mp hI).1]
  exact mul_le_mul hpow (Real.exp_le_exp.mpr hphase) (Real.exp_pos _).le
    (pow_nonneg ((sub_pos.mpr htop).le.trans hdist) _)

theorem closedRectangle_measurable (tl tr sb st : ℝ) : MeasurableSet (closedRectangle tl tr sb st) := by
  have h0 : IsClosed ((fun p : Coord => p 0) ⁻¹' Icc tl tr) := isClosed_Icc.preimage (continuous_apply 0)
  have h1 : IsClosed ((fun p : Coord => p 1) ⁻¹' Icc sb st) := isClosed_Icc.preimage (continuous_apply 1)
  exact (h0.inter h1).measurableSet

theorem coordinateSubsetIntegral_closedRectangle (tl tr sb st : ℝ) (F : Coord → ℝ)
    (ht : tl ≤ tr) (hs : sb ≤ st) (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    coordinateSubsetIntegral (closedRectangle tl tr sb st) F = rectangleIntegral tl tr sb st F := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hpre : (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' closedRectangle tl tr sb st =
      Icc tl tr ×ˢ Icc sb st := by
    ext q
    simp [closedRectangle,boxPoint,Prod.le_def,and_left_comm,and_assoc]
  unfold coordinateSubsetIntegral
  rw [hpre]

theorem capInterior_gradient_le_directed_energy
    {L R bottom top b lambda MI : ℝ} {I u : Coord → ℝ}
    (hL : -2 < L) (hR : R < 2) (hbottom : -2 < bottom)
    (hLR : L ≤ R) (hbt : bottom ≤ top) (htop : top < b) (hb : b ≤ 0)
    (hlambda : 0 ≤ lambda) (hI : ContDiffOn ℝ ∞ I capChartDomain)
    (hu : ContDiffOn ℝ ∞ u capChartDomain)
    (hIv : ∀ p ∈ closedRectangle L R bottom top, |I p| ≤ MI) :
    rectangleIntegral L R bottom top (fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
      (1/capInteriorWeightFloor top b lambda MI)*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
          (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) := by
  let F := fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2
  let E := directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda
  let S := closedRectangle L R bottom top
  let T := closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
  have hwpos := capInteriorWeightFloor_pos (lambda := lambda) (MI := MI) htop
  obtain ⟨htlo,htwidth,htone,hrone,hrwidth,htrhi,hsblo,hswidth,hsone,hlt,hrt⟩ :=
    capOuterRectangle_edges hL hR hbottom
  have ht : capOuterLeft L ≤ capOuterRight R := by linarith
  have hs : capOuterBottom bottom ≤ b := by linarith
  have hT : T ⊆ capChartDomain := capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hST : S ⊆ T := by
    intro p hp
    exact ⟨⟨hlt.le.trans hp.1.1,hp.1.2.trans hrt.le⟩,
      ⟨(by linarith [hp.2.1]),hp.2.2.trans htop.le⟩⟩
  have hgrad := ((partial_contDiffOn hu capChartDomain_isOpen 0).pow 2).add
    ((partial_contDiffOn hu capChartDomain_isOpen 1).pow 2)
  have hFc : ContinuousOn F T := hgrad.continuousOn.mono hT
  have hEc : ContinuousOn E T :=
    ((((capSpatialCutoff_contDiff L R bottom).contDiffOn.mul
      (directedWeight_contDiffOn b lambda hI)).mul hgrad).continuousOn.mono hT)
  have hEn (p : Coord) (hp : p ∈ T) : 0 ≤ E p := by
    have hchi := (capSpatialCutoff_range L R bottom p).1
    have hd : 0 ≤ edgeDistance b p := sub_nonneg.mpr hp.2.2
    unfold E directedGradientEnergy directedWeight
    positivity
  have hpoint (p : Coord) (hp : p ∈ S) : F p ≤ (1/capInteriorWeightFloor top b lambda MI)*E p := by
    have hW := directedWeight_interior_lower htop hlambda hp.2.2 (hIv p hp)
    have hchi := capSpatialCutoff_one hL hR hbottom p ⟨hp.1.1,hp.1.2,hp.2.1⟩
    have hgrad0 : 0 ≤ F p := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right hW hgrad0
    have hscaled : capInteriorWeightFloor top b lambda MI*F p ≤ E p := by
      simpa only [E,directedGradientEnergy,hchi,one_mul] using hh
    have hdiv : F p ≤ E p/capInteriorWeightFloor top b lambda MI :=
      (le_div_iff₀ hwpos).mpr (by simpa only [mul_comm] using hscaled)
    convert hdiv using 1
    ring
  have hcomp := restricted_gradient_from_energy ht hs (closedRectangle_measurable _ _ _ _)
    hST hFc hEc hEn (show 0 ≤ 1/capInteriorWeightFloor top b lambda MI by positivity) hpoint
  rw [coordinateSubsetIntegral_closedRectangle L R bottom top F hLR hbt (hFc.mono hST)] at hcomp
  exact hcomp

end SmoothLocal.Weighted

end

end OAI
