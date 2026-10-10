import OAI.Dynamics.StandardMap.RealBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
def NonaffineLine (d : ℝ → ℝ → ℝ) : Prop := ¬∃w:ℝ,∀x y:ℝ,d x y=w*|y-x|
lemma nonaffine_realArray (d : NonAffineArray) (hu : UnitArray d.val) : NonaffineLine (realArray d.val) := by
  rintro ⟨w,hw⟩
  have hb : w∈Icc (0:ℝ) 1 := by
    have h0 := realArray_nonneg d.val hu 0 1
    have h1 := realArray_le d.val hu 0 1
    rw [hw] at h0 h1
    norm_num at h0 h1
    exact ⟨h0,h1⟩
  apply d.property
  refine ⟨⟨w,hb⟩,?_⟩
  apply Subtype.ext
  funext s t
  change w*|(t:ℝ)-(s:ℝ)|=d.val.val s t
  simpa only [realArray_coe d.val hu] using (hw s t).symm
lemma connected_affine_full {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (U : Set ℝ) (hU : IsPreconnected U) (x : U)
    (hl : ∀y∈U,∃w,LocallyAffineAt d y w) :
    ∃w:ℝ,0≤ w ∧ w≤1 ∧ (∀y∈U,LocallyAffineAt d y w) ∧ (∀a∈U,∀b∈U,d a b=w*|b-a|) := by
  obtain ⟨w,hw⟩ := connected_local_speed U hU x (fun y => hl y y.property)
  have hb := locallyAffine_speed_bounds hd (hw x)
  refine ⟨w,hb.1,hb.2,fun y hy => hw ⟨y,hy⟩,?_⟩
  intro a ha b hb'
  rcases lt_trichotomy a b with hab|rfl|hab
  · rw [abs_of_pos (sub_pos.mpr hab)]
    exact tree_affine_of_fixed_local_speed hd a b w hab hb.1
      (fun y hy => hw ⟨y,hU.ordConnected.out ha hb' hy⟩)
  · simp only [hd.self,sub_self,abs_zero,mul_zero]
  · rw [hd.symm,abs_sub_comm,abs_of_pos (sub_pos.mpr hab)]
    exact tree_affine_of_fixed_local_speed hd b a w hab hb.1
      (fun y hy => hw ⟨y,hU.ordConnected.out hb' ha hy⟩)
lemma affine_component_data {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (hn : NonaffineLine d)
    {x : ℝ} (hx : x∈locallyAffineSet d) :
    ∃w:ℝ,0≤ w ∧ w≤1 ∧
      (∀y∈connectedComponentIn (locallyAffineSet d) x,LocallyAffineAt d y w) ∧
      (∀a∈connectedComponentIn (locallyAffineSet d) x,∀b∈connectedComponentIn (locallyAffineSet d) x,d a b=w*|b-a|) ∧
      connectedComponentIn (locallyAffineSet d) x≠univ := by
  obtain ⟨w,hw0,hw1,hl,ha⟩ := connected_affine_full hd _ isPreconnected_connectedComponentIn
    ⟨x,mem_connectedComponentIn hx⟩ (fun y hy => connectedComponentIn_subset (locallyAffineSet d) x hy)
  refine ⟨w,hw0,hw1,hl,ha,?_⟩
  intro he
  exact hn ⟨w,fun a b => ha a (by rw [he]; trivial) b (by rw [he]; trivial)⟩
lemma fast_component_speed_one {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x w : ℝ}
    (hp : SlowPair d c) (hw : LocallyAffineAt d x w) (hfast : c< w) : w=1 := by
  have hx : x∈locallyAffineSet d := ⟨w,hw⟩
  let U := connectedComponentIn (locallyAffineSet d) x
  have ho : IsOpen U := (isOpen_locallyAffineSet d).connectedComponentIn
  have hxm : x∈U := mem_connectedComponentIn hx
  obtain ⟨v,hv0,hv1,hl,ha,hne⟩ := affine_component_data hd hn hx
  have hvw : v=w := locallyAffine_speed_unique (hl x hxm) hw
  subst v
  have hcl := affineOn_closure hc U w ha
  obtain ⟨z,hz⟩ := nonempty_frontier_iff.mpr ⟨⟨x,hxm⟩,hne⟩
  have hzp : ¬∃v,LocallyAffineAt d z v := frontier_component_not_mem (isOpen_locallyAffineSet d) hx hz
  have hzx : z≠x := by
    intro he; subst z
    apply hz.2
    rwa [ho.interior_eq]
  by_contra hn1
  have hxq : ¬LocallyAffineAt d x 1 := fun h => hn1 (locallyAffine_speed_unique hw h)
  have hh := hp z x hzp hxq
  rw [hcl z hz.1 x (subset_closure hxm)] at hh
  have habs : 0 < |x-z| := abs_pos.mpr (sub_ne_zero.mpr hzx.symm)
  nlinarith
lemma fast_local_ray {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x w : ℝ}
    (hp : SlowPair d c) (hc1 : c<1) (hw : LocallyAffineAt d x w) (hfast : c< w) :
    (∃a:ℝ,x< a ∧ (¬∃v,LocallyAffineAt d a v) ∧ ∀s≤ a,∀t≤ a,d s t=|t-s|) ∨
    (∃a:ℝ,a< x ∧ (¬∃v,LocallyAffineAt d a v) ∧ ∀s≥a,∀t≥a,d s t=|t-s|) := by
  have hx : x∈locallyAffineSet d := ⟨w,hw⟩
  have hw1 := fast_component_speed_one hd hc hn hp hw hfast
  let U := connectedComponentIn (locallyAffineSet d) x
  have ho : IsOpen U := (isOpen_locallyAffineSet d).connectedComponentIn
  have hxm : x∈U := mem_connectedComponentIn hx
  have hU : IsPreconnected U := isPreconnected_connectedComponentIn
  obtain ⟨v,hv0,hv1,hl,ha,hne⟩ := affine_component_data hd hn hx
  have hvw : v=w := locallyAffine_speed_unique (hl x hxm) hw
  have hvone : v=1 := hvw.trans hw1
  rw [hvone] at ha
  have hcl := affineOn_closure hc U 1 ha
  have hfront (a b : ℝ) (ha : a∈frontier U) (hb : b∈frontier U) : a=b := by
    have hpa : ¬∃v,LocallyAffineAt d a v := frontier_component_not_mem (isOpen_locallyAffineSet d) hx ha
    have hpb : ¬∃v,LocallyAffineAt d b v := frontier_component_not_mem (isOpen_locallyAffineSet d) hx hb
    have hh := hp a b hpa (fun h => hpb ⟨1,h⟩)
    rw [hcl a ha.1 b hb.1,one_mul] at hh
    have he : |b-a|=0 := by nlinarith [abs_nonneg (b-a)]
    exact (sub_eq_zero.mp (abs_eq_zero.mp he)).symm
  by_cases hlo : BddBelow U
  · have hinf := open_nonempty_inf_frontier ho ⟨x,hxm⟩ hlo
    have hhi : ¬BddAbove U := by
      intro hhi
      have he := hfront _ _ hinf (open_nonempty_sup_frontier ho ⟨x,hxm⟩ hhi)
      have h1 := open_inf_lt_mem ho hlo hxm
      have h2 := open_mem_lt_sup ho hhi hxm
      linarith
    have he := open_ordConnected_eq_Ioi ho hU.ordConnected ⟨x,hxm⟩ hlo hhi
    refine Or.inr ⟨sInf U,open_inf_lt_mem ho hlo hxm,frontier_component_not_mem (isOpen_locallyAffineSet d) hx hinf,?_⟩
    intro s hs t ht
    have hclosure : closure U=Ici (sInf U) := (congrArg closure he).trans (closure_Ioi _)
    simpa only [one_mul] using hcl s (by rw [hclosure]; exact hs) t (by rw [hclosure]; exact ht)
  · have hhi : BddAbove U := by
      by_contra hh
      exact hne (ordConnected_eq_univ_of_unbounded hU.ordConnected hlo hh)
    have hsup := open_nonempty_sup_frontier ho ⟨x,hxm⟩ hhi
    have he := open_ordConnected_eq_Iio ho hU.ordConnected ⟨x,hxm⟩ hlo hhi
    refine Or.inl ⟨sSup U,open_mem_lt_sup ho hhi hxm,frontier_component_not_mem (isOpen_locallyAffineSet d) hx hsup,?_⟩
    intro s hs t ht
    have hclosure : closure U=Iic (sSup U) := (congrArg closure he).trans (closure_Iio _)
    simpa only [one_mul] using hcl s (by rw [hclosure]; exact hs) t (by rw [hclosure]; exact ht)
end StandardMapEntropy

end OAI
