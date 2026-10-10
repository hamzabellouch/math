import OAI.Analysis.LienardCycles.PeriodicMatching

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
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow
lemma IsPeriodicOrbit.eq_of_common {F : Polynomial ℝ} {C D : Set Plane}
    (hC : IsPeriodicOrbit F C) (hD : IsPeriodicOrbit F D) {p : Plane} (hp : p ∈ C) (hq : p ∈ D) : C=D := by
  obtain ⟨z,T,hz,_,_,_,rfl⟩ := hC
  obtain ⟨w,S,hw,_,_,_,rfl⟩ := hD
  obtain ⟨s,hs⟩ := hp
  obtain ⟨t,ht⟩ := hq
  have he := (hz.shift s).eq_of_eq (hw.shift t) (c:=0) (by simpa using hs.trans ht.symm)
  have hr (f : ℝ → Plane) (v : ℝ) : range (fun u=>f (u+v))=range f := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩;exact mem_range_self _
    · rintro ⟨u,rfl⟩;exact ⟨u-v,by simp⟩
  rw [←hr z s,he,hr]
lemma IsSolution.oval_at_max {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T)
    {s t : ℝ} (hs : (z s).1=0) (ht : (z t).1=0)
    (hb : ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2) :
    ∃ v w, IsRightExcursion z t v ∧ IsRightExcursion (QuinticLienard.reverseX z) (-w) (-v) ∧ z w=z t := by
  have hsign := hz.y_extrema_signs hn hT hp hs ht hb
  obtain ⟨v,hv⟩ := hz.right_excursion_after hn hT hp ht hsign.2
  obtain ⟨H,hH,hHl,hHr⟩ := hv.axis_peak hF hz hn
  obtain ⟨K,hK,hKl,hKr⟩ := hz.right_peak_at_extrema hF hn hT hp hs ht hb
  have hHK : H=K := (axisUpper_strictMono a).injOn hH hK (hHr.trans hKr.symm)
  have hvmin : (z v).2=(z s).2 := by rw [←hHl,hHK,hKl]
  obtain ⟨u,hu⟩ := hz.reverseX.right_excursion_before (reverseX_nonconstant hn) hT (reverseX_periodic hp)
    (t:=-v) (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg hv.right)
    (by simpa [QuinticLienard.reverseX,polynomialReflect_eval,hvmin] using hsign.1)
  obtain ⟨L,hL,hLl,hLr⟩ := hu.axis_peak (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly]) hz.reverseX (reverseX_nonconstant hn)
  obtain ⟨M,hM,hMl,hMr⟩ := hz.reverseX.right_peak_at_extrema (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly])
    (reverseX_nonconstant hn) hT (reverseX_periodic hp) (s:=-s) (t:=-t)
    (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg hs)
    (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg ht)
    (fun v=>by simpa [QuinticLienard.reverseX] using hb (-v))
  simp only [QuinticLienard.reverseX,neg_neg] at hLl hLr hMl hMr
  have hLM : L=M := (axisLower_strictAnti (reflectX a)).injOn hL hM (by rw [hLl,hMl,hvmin])
  refine ⟨v,-u,hv,by simpa using hu,Prod.ext ?_ ?_⟩
  · have h := hu.left
    simp only [QuinticLienard.reverseX] at h
    rw [neg_eq_zero] at h
    exact h.trans ht.symm
  · rw [←hLr,hLM,hMr]
lemma IsPeriodicOrbit.oval {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    ∃ (z : ℝ → Plane) (S T : ℝ), IsSolution F z ∧ 0<S ∧ S<T ∧
      Function.Periodic z T ∧ IsRightExcursion z 0 S ∧
      IsRightExcursion (QuinticLienard.reverseX z) (-T) (-S) ∧ C=range z := by
  obtain ⟨z,P,hz,hP,hp,hn,rfl⟩ := hC
  obtain ⟨s,t,hs,ht,hb⟩ := hz.y_extrema hP hp
  obtain ⟨v,w,hv,hw,he⟩ := hz.oval_at_max hF hn hP hp hs ht hb
  let f := fun u=>z (u+t)
  have hvw : v<w := by linarith [hw.lt]
  have hf : IsSolution F f := hz.shift t
  refine ⟨f,v-t,w-t,hf,sub_pos.mpr hv.lt,sub_lt_sub_right hvw _,?_,?_,?_,?_⟩
  · exact hf.periodic_of_hit (s:=0) (by simpa [f] using he)
  · refine ⟨by linarith [hv.lt],by simpa [f] using hv.left,by simpa [f] using hv.right,?_⟩
    intro u hu
    exact hv.positive (u+t) ⟨by linarith [hu.1],by linarith [hu.2]⟩
  · refine ⟨by linarith,?_,?_,?_⟩
    · simpa [QuinticLienard.reverseX,f] using hw.left
    · simpa [QuinticLienard.reverseX,f] using hw.right
    · intro u hu
      have H := hw.positive (u-t) ⟨by linarith [hu.1],by linarith [hu.2]⟩
      simpa [QuinticLienard.reverseX,f,sub_eq_add_neg,add_comm] using H
  · ext p
    constructor
    · rintro ⟨u,rfl⟩; exact ⟨u-t,by simp [f]⟩
    · rintro ⟨u,rfl⟩; exact mem_range_self _
end QuinticLienard

end OAI
