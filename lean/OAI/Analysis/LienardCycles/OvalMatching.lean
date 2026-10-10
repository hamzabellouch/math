import OAI.Analysis.LienardCycles.ReturnMatching

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow RealAnalysis
lemma IsRightExcursion.nonconstant {z : ℝ → Plane} {s t : ℝ} (hr : IsRightExcursion z s t) : ∃ u v,z u≠z v := by
  refine ⟨s,(s+t)/2,?_⟩
  intro he
  have hh := hr.positive ((s+t)/2) ⟨by linarith [hr.lt],by linarith [hr.lt]⟩
  rw [←he,hr.left] at hh
  exact lt_irrefl _ hh
lemma IsSolution.oval_axis_positive {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    {S T : ℝ} (hS : 0<S) (hST : S<T) (hp : Function.Periodic z T)
    (hr : IsRightExcursion z 0 S) (hl : IsRightExcursion (QuinticLienard.reverseX z) (-T) (-S))
    {p : Plane} (hpr : p ∈ range z) (hpx : p.1=0) (hpy : F.eval 0<p.2) : p=z 0 := by
  have hT := hS.trans hST
  have hsign := hr.endpoint_signs hz hr.nonconstant
  have hzT : z T=z 0 := by simpa using hp 0
  rw [←hp.image_Icc hT 0] at hpr
  obtain ⟨t,ht,rfl⟩ := hpr
  simp only [zero_add,mem_Icc] at ht
  rcases eq_or_lt_of_le ht.1 with he|he
  · rw [←he]
  rcases eq_or_lt_of_le ht.2 with heT|heT
  · rw [heT,hzT]
  rcases lt_trichotomy t S with hs|hs|hs
  · exact False.elim ((ne_of_gt (hr.positive t ⟨he,hs⟩)) hpx)
  · subst t
    exact False.elim ((not_lt_of_ge hsign.1.le) hpy)
  · have hx := hl.positive (-t) ⟨by linarith,by linarith⟩
    simp only [QuinticLienard.reverseX,neg_neg,hpx,neg_zero] at hx
    exact False.elim (lt_irrefl _ hx)
lemma IsSolution.oval_matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} (hz : IsSolution F z)
    {S T : ℝ} (hp : Function.Periodic z T)
    (hr : IsRightExcursion z 0 S) (hl : IsRightExcursion (QuinticLienard.reverseX z) (-T) (-S)) :
    let r := ((z 0).2-(z S).2)/2
    r ∈ matchingDomain a (reflectX a) ∧ matchingDelta a (reflectX a) r=0 ∧ poly a 0+axisM a r+r=(z 0).2 := by
  have hzT : z T=z 0 := by simpa using hp 0
  obtain ⟨H,hH,hHa,hHb⟩ := hr.axis_peak hF hz hr.nonconstant
  obtain ⟨K,hK,hKa,hKb⟩ := hl.axis_peak (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly]) hz.reverseX (reverseX_nonconstant hr.nonconstant)
  simp only [QuinticLienard.reverseX,neg_neg,hzT] at hKa hKb
  dsimp only
  have hwH : axisWidth a H=((z 0).2-(z S).2)/2 := by rw [axisWidth,hHa,hHb]
  have hwK : axisWidth (reflectX a) K=((z 0).2-(z S).2)/2 := by rw [axisWidth,hKa,hKb]
  have hpa := axisPeak_eq a hH hwH
  have hpb := axisPeak_eq (reflectX a) hK hwK
  have hM : axisM a (((z 0).2-(z S).2)/2)=((z 0).2+(z S).2)/2-poly a 0 := by
    rw [axisM,hpa,axisCenter,hHa,hHb]
  have hMb : axisM (reflectX a) (((z 0).2-(z S).2)/2)=((z 0).2+(z S).2)/2-poly a 0 := by
    rw [axisM,hpb,axisCenter,hKa,hKb,reflectX_poly]
    simp
  refine ⟨⟨⟨H,hH,hwH⟩,⟨K,hK,hwK⟩⟩,?_,?_⟩
  · rw [matchingDelta,hM,hMb,sub_self]
  · rw [hM];ring
end QuinticLienard

end OAI
