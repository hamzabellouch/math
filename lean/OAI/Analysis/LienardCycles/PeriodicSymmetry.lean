import OAI.Analysis.LienardCycles.ExcursionSigns

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
noncomputable def polynomialReflect (F : Polynomial ℝ) : Polynomial ℝ := F.comp (-Polynomial.X)
@[simp] lemma polynomialReflect_eval (F : Polynomial ℝ) (x : ℝ) : (polynomialReflect F).eval x=F.eval (-x) := by
  simp [polynomialReflect]
def reverseY (z : ℝ → Plane) (t : ℝ) : Plane := ((z (-t)).1,-(z (-t)).2)
def reverseX (z : ℝ → Plane) (t : ℝ) : Plane := (-(z (-t)).1,(z (-t)).2)
lemma IsSolution.reverseY {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) :
    IsSolution (-F) (reverseY z) := by
  intro t
  have hx := (hz.x_deriv (-t)).scomp t (hasDerivAt_id t).neg
  have hy := (hz.y_deriv (-t)).scomp t (hasDerivAt_id t).neg
  convert! hx.prodMk hy.neg using 1
  simp [QuinticLienard.reverseY,vectorField]
  ring
lemma IsSolution.reverseX {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) :
    IsSolution (polynomialReflect F) (reverseX z) := by
  intro t
  have hx := (hz.x_deriv (-t)).scomp t (hasDerivAt_id t).neg
  have hy := (hz.y_deriv (-t)).scomp t (hasDerivAt_id t).neg
  convert! hx.neg.prodMk hy using 1; simp [QuinticLienard.reverseX,vectorField]
lemma reverseY_nonconstant {z : ℝ → Plane} (hn : ∃ s t,z s≠z t) : ∃ s t,reverseY z s≠reverseY z t := by
  obtain ⟨s,t,hst⟩ := hn
  refine ⟨-s,-t,fun h=>hst (Prod.ext ?_ ?_)⟩
  · simpa [QuinticLienard.reverseY] using congrArg Prod.fst h
  · simpa [QuinticLienard.reverseY] using congrArg (fun p : Plane=> -p.2) h
lemma reverseX_nonconstant {z : ℝ → Plane} (hn : ∃ s t,z s≠z t) : ∃ s t,reverseX z s≠reverseX z t := by
  obtain ⟨s,t,hst⟩ := hn
  refine ⟨-s,-t,fun h=>hst (Prod.ext ?_ ?_)⟩
  · simpa [QuinticLienard.reverseX] using congrArg (fun p : Plane=> -p.1) h
  · simpa [QuinticLienard.reverseX] using congrArg Prod.snd h
lemma reverseY_periodic {z : ℝ → Plane} {T : ℝ} (hp : Function.Periodic z T) : Function.Periodic (reverseY z) T := by
  intro t
  simp only [QuinticLienard.reverseY,neg_add]
  rw [hp.neg (-t)]
lemma reverseX_periodic {z : ℝ → Plane} {T : ℝ} (hp : Function.Periodic z T) : Function.Periodic (reverseX z) T := by
  intro t
  simp only [QuinticLienard.reverseX,neg_add]
  rw [hp.neg (-t)]
lemma IsSolution.right_excursion_before {F : Polynomial ℝ} {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T)
    (hp : Function.Periodic z T) {t : ℝ} (ht : (z t).1=0) (hy : (z t).2<F.eval 0) :
    ∃ s,IsRightExcursion z s t := by
  obtain ⟨s,hs⟩ := hz.reverseY.right_excursion_after (reverseY_nonconstant hn) hT (reverseY_periodic hp)
    (s:=-t) (by simpa [QuinticLienard.reverseY] using ht) (by simpa [QuinticLienard.reverseY] using neg_lt_neg hy)
  refine ⟨-s,by linarith [hs.lt],?_,ht,?_⟩
  · exact hs.right
  · intro v hv
    have H := hs.positive (-v) ⟨by linarith [hv.2],by linarith [hv.1]⟩
    simpa [QuinticLienard.reverseY] using H
lemma IsSolution.y_extrema {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T) :
    ∃ s t,(z s).1=0 ∧ (z t).1=0 ∧ ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2 := by
  obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT.le) hz.continuous.snd.continuousOn
  obtain ⟨t,ht,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT.le) hz.continuous.snd.continuousOn
  have hb (v : ℝ) : (z s).2≤(z v).2 ∧ (z v).2≤(z t).2 := by
    have hv : z v ∈ z '' Icc 0 T := by rw [show Icc 0 T=Icc 0 (0+T) by simp,hp.image_Icc hT 0];exact mem_range_self v
    obtain ⟨w,hw,he⟩ := hv
    rw [←he]
    exact ⟨hmin hw,hmax hw⟩
  have hsd := (show IsLocalMin (fun v=>(z v).2) s from Filter.Eventually.of_forall fun v=>(hb v).1).hasDerivAt_eq_zero (hz.y_deriv s)
  have htd := (show IsLocalMax (fun v=>(z v).2) t from Filter.Eventually.of_forall fun v=>(hb v).2).hasDerivAt_eq_zero (hz.y_deriv t)
  exact ⟨s,t,neg_eq_zero.mp hsd,neg_eq_zero.mp htd,hb⟩
end QuinticLienard

end OAI
