import OAI.Analysis.LienardCycles.ExcursionAxis

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
lemma IsSolution.y_extrema_signs {F : Polynomial ℝ} {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T)
    {s t : ℝ} (hs : (z s).1=0) (ht : (z t).1=0)
    (hb : ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2) : (z s).2<F.eval 0 ∧ F.eval 0<(z t).2 := by
  constructor
  · by_contra! h
    have hlt : F.eval 0<(z s).2 := lt_of_le_of_ne h (hz.axis_transverse hn hs).symm
    obtain ⟨v,hv⟩ := hz.right_excursion_after hn hT hp hs hlt
    exact (not_lt_of_ge (hb v).1) (hv.y_lt hz)
  · by_contra! h
    have hlt : (z t).2<F.eval 0 := lt_of_le_of_ne h (hz.axis_transverse hn ht)
    obtain ⟨v,hv⟩ := hz.right_excursion_before hn hT hp ht hlt
    exact (not_lt_of_ge (hb v).2) (hv.y_lt hz)
lemma IsSolution.right_peak_at_extrema {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T)
    {s t : ℝ} (hs : (z s).1=0) (ht : (z t).1=0)
    (hb : ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2) :
    ∃ H ∈ transversePeaks a,axisEndpoint a false H=(z s).2 ∧ axisEndpoint a true H=(z t).2 := by
  have hsign := hz.y_extrema_signs hn hT hp hs ht hb
  obtain ⟨v,hv⟩ := hz.right_excursion_after hn hT hp ht hsign.2
  obtain ⟨w,hw⟩ := hz.right_excursion_before hn hT hp hs hsign.1
  obtain ⟨H,hH,hHl,hHr⟩ := hv.axis_peak hF hz hn
  obtain ⟨K,hK,hKl,hKr⟩ := hw.axis_peak hF hz hn
  have hcomp : axisEndpoint a true K≤axisEndpoint a true H := by rw [hKr,hHr];exact (hb w).2
  have hc := (axis_order hK hH).mp hcomp
  rw [hHl,hKl] at hc
  exact ⟨H,hH,hHl.trans (le_antisymm hc (hb v).1),hHr⟩
lemma IsSolution.matching_at_extrema {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T)
    {s t : ℝ} (hs : (z s).1=0) (ht : (z t).1=0)
    (hb : ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2) :
    let r := ((z t).2-(z s).2)/2
    r ∈ matchingDomain a (reflectX a) ∧ matchingDelta a (reflectX a) r=0 ∧
      axisM a r=((z t).2+(z s).2)/2-poly a 0 := by
  obtain ⟨H,hH,hHl,hHr⟩ := hz.right_peak_at_extrema hF hn hT hp hs ht hb
  obtain ⟨K,hK,hKl,hKr⟩ := hz.reverseX.right_peak_at_extrema
    (a:=reflectX a) (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly])
    (reverseX_nonconstant hn) hT (reverseX_periodic hp) (s:=-s) (t:=-t)
    (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg hs) (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg ht)
    (fun v=>by simpa [QuinticLienard.reverseX] using hb (-v))
  simp only [QuinticLienard.reverseX,neg_neg] at hKl hKr
  dsimp only
  have hwH : axisWidth a H=((z t).2-(z s).2)/2 := by rw [axisWidth,hHl,hHr]
  have hwK : axisWidth (reflectX a) K=((z t).2-(z s).2)/2 := by rw [axisWidth,hKl,hKr]
  have hpa := axisPeak_eq a hH hwH
  have hpb := axisPeak_eq (reflectX a) hK hwK
  have hM : axisM a (((z t).2-(z s).2)/2)=((z t).2+(z s).2)/2-poly a 0 := by
    rw [axisM,hpa,axisCenter,hHl,hHr]
  have hMb : axisM (reflectX a) (((z t).2-(z s).2)/2)=((z t).2+(z s).2)/2-poly a 0 := by
    rw [axisM,hpb,axisCenter,hKl,hKr,reflectX_poly]
    simp
  refine ⟨⟨⟨H,hH,hwH⟩,⟨K,hK,hwK⟩⟩,?_,hM⟩
  rw [matchingDelta,hM,hMb,sub_self]
lemma IsPeriodicOrbit.matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    ∃ r ∈ matchingDomain a (reflectX a),matchingDelta a (reflectX a) r=0 ∧
      (0,poly a 0+axisM a r+r) ∈ C ∧
      ∀ p ∈ C,poly a 0+axisM a r-r≤p.2 ∧ p.2≤poly a 0+axisM a r+r := by
  obtain ⟨z,T,hz,hT,hp,hn,rfl⟩ := hC
  obtain ⟨s,t,hs,ht,hb⟩ := hz.y_extrema hT hp
  obtain ⟨hr,hd,hM⟩ := hz.matching_at_extrema hF hn hT hp hs ht hb
  refine ⟨((z t).2-(z s).2)/2,hr,hd,?_,?_⟩
  · refine ⟨t,?_⟩
    apply Prod.ext ht
    rw [hM]
    ring
  · rintro p ⟨v,rfl⟩
    rw [hM]
    constructor <;> linarith [(hb v).1,(hb v).2]
end QuinticLienard

end OAI
