import OAI.Dynamics.StandardMap.WeightBalance

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy

noncomputable def leftEndpoint (d : DistanceArray) : EReal :=
  ⨅s:DyadicTime,⨅t:DyadicTime,if d.val s t≠|(t:ℝ)-(s:ℝ)| then ((max (s:ℝ) (t:ℝ)):EReal) else ⊤
noncomputable def rightEndpoint (d : DistanceArray) : EReal :=
  ⨆s:DyadicTime,⨆t:DyadicTime,if d.val s t≠|(t:ℝ)-(s:ℝ)| then ((min (s:ℝ) (t:ℝ)):EReal) else ⊥
lemma measurable_leftEndpoint : Measurable leftEndpoint := by
  apply Measurable.iInf; intro s
  apply Measurable.iInf; intro t
  exact measurable_const.ite
    ((isClosed_eq (continuous_arrayEval s t) continuous_const).measurableSet.compl) measurable_const
lemma measurable_rightEndpoint : Measurable rightEndpoint := by
  apply Measurable.iSup; intro s
  apply Measurable.iSup; intro t
  exact measurable_const.ite
    ((isClosed_eq (continuous_arrayEval s t) continuous_const).measurableSet.compl) measurable_const
lemma leftEndpoint_le_of_nonunit (d : DistanceArray) {s t : DyadicTime}
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : leftEndpoint d≤((max (s:ℝ) (t:ℝ)):EReal) := by
  unfold leftEndpoint
  exact (iInf_le_of_le s (iInf_le_of_le t (by rw [ite_eq_left h])))
lemma le_rightEndpoint_of_nonunit (d : DistanceArray) {s t : DyadicTime}
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : ((min (s:ℝ) (t:ℝ)):EReal)≤rightEndpoint d := by
  unfold rightEndpoint
  exact (le_iSup_of_le s (le_iSup_of_le t (by rw [ite_eq_left h])))
lemma le_leftEndpoint_iff (d : DistanceArray) (a : EReal) : a≤leftEndpoint d ↔
    ∀s t:DyadicTime,d.val s t≠|(t:ℝ)-(s:ℝ)| → a≤((max (s:ℝ) (t:ℝ)):EReal) := by
  simp only [leftEndpoint,le_iInf_iff]
  constructor
  · intro h s t hn; simpa only [ite_eq_left hn] using h s t
  · intro h s t; split_ifs with hn
    · exact h s t hn
    · exact le_top
lemma rightEndpoint_le_iff (d : DistanceArray) (a : EReal) : rightEndpoint d≤a ↔
    ∀s t:DyadicTime,d.val s t≠|(t:ℝ)-(s:ℝ)| → ((min (s:ℝ) (t:ℝ)):EReal)≤a := by
  simp only [rightEndpoint,iSup_le_iff]
  constructor
  · intro h s t hn; simpa only [ite_eq_left hn] using h s t
  · intro h s t; split_ifs with hn
    · exact h s t hn
    · exact bot_le
lemma leftEndpoint_lower_ray (d : DistanceArray) {a : ℝ}
    (h : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) : (a:EReal)≤leftEndpoint d := by
  apply (le_leftEndpoint_iff d a).mpr
  intro s t hn
  have hh : a < max (s:ℝ) (t:ℝ) := by
    by_contra hm
    have hm' := le_of_not_gt hm
    exact hn (h s t ((le_max_left _ _).trans hm') ((le_max_right _ _).trans hm'))
  exact EReal.coe_le_coe_iff.mpr hh.le
lemma rightEndpoint_upper_ray (d : DistanceArray) {b : ℝ}
    (h : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) : rightEndpoint d≤(b:EReal) := by
  apply (rightEndpoint_le_iff d b).mpr
  intro s t hn
  have hh : min (s:ℝ) (t:ℝ)<b := by
    by_contra hm
    have hm' := le_of_not_gt hm
    exact hn (h s t (hm'.trans (min_le_left _ _)) (hm'.trans (min_le_right _ _)))
  exact EReal.coe_le_coe_iff.mpr hh.le
end StandardMapEntropy

end OAI
