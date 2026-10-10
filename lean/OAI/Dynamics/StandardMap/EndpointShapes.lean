import OAI.Dynamics.StandardMap.EndpointDefinition

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma dyadic_between {a b : ℝ} (hab : a < b) : ∃s : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < b := by
  obtain ⟨x,⟨s,rfl⟩,ha,hb⟩ := dyadicTime_dense.exists_between hab
  exact ⟨s,ha,hb⟩
lemma dyadic_pair_between {a b : ℝ} (hab : a < b) :
    ∃s t : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < (t:ℝ) ∧ (t:ℝ) < b := by
  obtain ⟨s,has,hsb⟩ := dyadic_between hab
  obtain ⟨t,hst,htb⟩ := dyadic_between hsb
  exact ⟨s,t,has,hst,htb⟩
lemma nonunit_of_slow {d : DistanceArray} {c : ℝ} (hc : c < 1) {s t : DyadicTime}
    (hst : (s:ℝ) < (t:ℝ)) (h : d.val s t ≤ c*((t:ℝ)-(s:ℝ))) : d.val s t ≠ |(t:ℝ)-(s:ℝ)| := by
  rw [abs_of_pos (sub_pos.mpr hst)]
  intro he
  have hp := mul_lt_mul_of_pos_right hc (sub_pos.mpr hst)
  nlinarith
lemma leftEndpoint_le_of_slow_interval {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d ≤ (a:EReal) := by
  by_contra hn
  obtain ⟨r,har,hr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have har' : a < r := EReal.coe_lt_coe_iff.mp har
  obtain ⟨s,t,has,hst,htb⟩ := dyadic_pair_between (lt_min har' hab)
  have htb' := (lt_min_iff.mp htb).2
  have htr := (lt_min_iff.mp htb).1
  have hs := h s t ⟨has.le,(hst.trans htb').le⟩ ⟨(has.trans hst).le,htb'.le⟩
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hu := leftEndpoint_le_of_nonunit d (nonunit_of_slow hc hst hs)
  rw [max_eq_right (EReal.coe_le_coe_iff.mpr hst.le)] at hu
  exact (not_le_of_gt hr) (hu.trans (EReal.coe_le_coe_iff.mpr htr.le))
lemma rightEndpoint_ge_of_slow_interval {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
    (b:EReal) ≤ rightEndpoint d := by
  by_contra hn
  obtain ⟨r,hr,hrb⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hrb' : r < b := EReal.coe_lt_coe_iff.mp hrb
  obtain ⟨s,t,has,hst,htb⟩ := dyadic_pair_between (max_lt hrb' hab)
  have has' := (max_lt_iff.mp has).2
  have hrs := (max_lt_iff.mp has).1
  have hs := h s t ⟨has'.le,(hst.trans htb).le⟩ ⟨(has'.trans hst).le,htb.le⟩
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hu := le_rightEndpoint_of_nonunit d (nonunit_of_slow hc hst hs)
  rw [min_eq_left (EReal.coe_le_coe_iff.mpr hst.le)] at hu
  exact (not_le_of_gt hr) ((EReal.coe_le_coe_iff.mpr hrs.le).trans hu)
lemma endpoints_slow {d : DistanceArray} {c : ℝ} (hc : c < 1)
    (h : ∀s t:DyadicTime,d.val s t≤c*|(t:ℝ)-(s:ℝ)|) : leftEndpoint d=⊥ ∧ rightEndpoint d=⊤ := by
  constructor
  · apply eq_bot_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,_,hr⟩ := EReal.exists_between_coe_real hh
    exact (not_le_of_gt hr) (leftEndpoint_le_of_slow_interval (a := r) (b := r+1) (by linarith) hc (fun s t _ _ => h s t))
  · apply eq_top_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hh
    exact (not_le_of_gt hr) (rightEndpoint_ge_of_slow_interval (a := r-1) (b := r) (by linarith) hc (fun s t _ _ => h s t))
lemma endpoints_left_ray {d : DistanceArray} {a c : ℝ} (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=⊤ := by
  constructor
  · exact le_antisymm (leftEndpoint_le_of_slow_interval (b := a+1) (by linarith) hc (fun s t hp hq => hs s t hp.1 hq.1))
      (leftEndpoint_lower_ray d hl)
  · apply eq_top_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hh
    have he := rightEndpoint_ge_of_slow_interval (d := d) (a := max r a) (b := max r a+1) (by linarith) hc
      (fun s t hp hq => hs s t ((le_max_right _ _).trans hp.1) ((le_max_right _ _).trans hq.1))
    exact (not_le_of_gt hr) ((EReal.coe_le_coe_iff.mpr (by linarith [le_max_left r a])).trans he)
lemma endpoints_right_ray {d : DistanceArray} {b c : ℝ} (hc : c < 1)
    (hr : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=⊥ ∧ rightEndpoint d=(b:EReal) := by
  constructor
  · apply eq_bot_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,_,hr'⟩ := EReal.exists_between_coe_real hh
    have he := leftEndpoint_le_of_slow_interval (d := d) (a := min r b-1) (b := min r b) (by linarith) hc
      (fun s t hp hq => hs s t (hp.2.trans (min_le_right _ _)) (hq.2.trans (min_le_right _ _)))
    exact (not_le_of_gt hr') (he.trans (EReal.coe_le_coe_iff.mpr (by linarith [min_le_left r b])))
  · exact le_antisymm (rightEndpoint_upper_ray d hr)
      (rightEndpoint_ge_of_slow_interval (a := b-1) (by linarith) hc (fun s t hp hq => hs s t hp.2 hq.2))
lemma endpoints_two_rays {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hr : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=(b:EReal) :=
  ⟨le_antisymm (leftEndpoint_le_of_slow_interval hab hc hs) (leftEndpoint_lower_ray d hl),
   le_antisymm (rightEndpoint_upper_ray d hr) (rightEndpoint_ge_of_slow_interval hab hc hs)⟩
end StandardMapEntropy

end OAI
