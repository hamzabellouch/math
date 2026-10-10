import OAI.Dynamics.StandardMap.LocalMidpointAffine

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma local_zero_tests_midpoint (d : DistanceArray) (hu : UnitArray d) (x r : ℝ)
    (hz : ∀ j : ArrayTestIndex,(j.val.1:ℝ)∈ball x r → (j.val.2:ℝ)∈ball x r → arrayTest j d=0) :
    MidpointAffineOn (realArray d) (ball x r) := by
  have hc := continuous_realArray d hu
  have hm : Continuous (fun p : ℝ × ℝ => (p.1+p.2)/2) := (continuous_fst.add continuous_snd).div_const 2
  have hh : ∀s t : ℝ,s∈ball x r → t∈ball x r → s< t →
      realArray d s ((s+t)/2)=realArray d s t/2 ∧
      realArray d ((s+t)/2) t=realArray d s t/2 := by
    apply isClosed_property2 (p := fun s t => s∈ball x r → t∈ball x r → s< t →
      realArray d s ((s+t)/2)=realArray d s t/2 ∧
      realArray d ((s+t)/2) t=realArray d s t/2) dyadicTime_dense
    · apply isClosed_imp (isOpen_ball.preimage continuous_fst)
      apply isClosed_imp (isOpen_ball.preimage continuous_snd)
      apply isClosed_imp (isOpen_lt continuous_fst continuous_snd)
      exact (isClosed_eq (hc.comp (continuous_fst.prodMk hm)) (hc.div_const 2)).inter
        (isClosed_eq (hc.comp (hm.prodMk continuous_snd)) (hc.div_const 2))
    · intro s t hs ht hst
      have hh := array_zero_test_halves s t hst d (hz ⟨(s,t),hst⟩ hs ht)
      change realArray d (s:ℝ) (dyadicMid s t:ℝ)=realArray d (s:ℝ) (t:ℝ)/2 ∧
        realArray d (dyadicMid s t:ℝ) (t:ℝ)=realArray d (s:ℝ) (t:ℝ)/2
      simpa only [realArray_coe d hu] using hh
  exact fun s hs t ht hst => hh s t hs ht hst
lemma local_positive_test (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d)
    (x : ℝ) (hx : ¬∃w,LocallyAffineAt (realArray d) x w) (r : ℝ) (hr : 0< r) :
    ∃ j : ArrayTestIndex,(j.val.1:ℝ)∈ball x r ∧ (j.val.2:ℝ)∈ball x r ∧ 0< arrayTest j d := by
  by_contra hn
  have hz : ∀j : ArrayTestIndex,(j.val.1:ℝ)∈ball x r → (j.val.2:ℝ)∈ball x r → arrayTest j d=0 := by
    intro j hs ht'
    exact le_antisymm (le_of_not_gt (fun hj => hn ⟨j,hs,ht',hj⟩)) (arrayTest_nonneg j d)
  exact hx (midpoint_ball_locallyAffine (realArray_treeLine d hu ht) (continuous_realArray d hu) x r hr
    (local_zero_tests_midpoint d hu x r hz))
lemma local_positive_shortfall (d : DistanceArray) (hu : UnitArray d)
    (x : ℝ) (hx : ¬LocallyAffineAt (realArray d) x 1) (r : ℝ) (hr : 0< r) :
    ∃j : ArrayTestIndex,(j.val.1:ℝ)∈ball x r ∧ (j.val.2:ℝ)∈ball x r ∧ 0< arrayShortfall j.val.1 j.val.2 d := by
  by_contra hn
  have hz (s t : DyadicTime) (hs : (s:ℝ)∈ball x r) (ht : (t:ℝ)∈ball x r) (hst : (s:ℝ)<(t:ℝ)) :
      d.val s t=(t:ℝ)-(s:ℝ) := by
    have h := le_of_not_gt (fun h : 0< arrayShortfall s t d => hn ⟨⟨(s,t),hst⟩,hs,ht,h⟩)
    have hlow : (t:ℝ)-(s:ℝ)≤ d.val s t := by
      unfold arrayShortfall at h
      have hh : 1≤ d.val s t/((t:ℝ)-(s:ℝ)) := by linarith
      simpa only [one_mul] using (le_div_iff₀ (sub_pos.mpr hst)).mp hh
    have hhigh := hu s t
    rw [abs_of_pos (sub_pos.mpr hst)] at hhigh
    exact le_antisymm hhigh hlow
  have hc := continuous_realArray d hu
  have hall : ∀s t : ℝ,s∈ball x r → t∈ball x r → s< t → realArray d s t=t-s := by
    apply isClosed_property2 (p := fun s t => s∈ball x r → t∈ball x r → s< t → realArray d s t=t-s) dyadicTime_dense
    · apply isClosed_imp (isOpen_ball.preimage continuous_fst)
      apply isClosed_imp (isOpen_ball.preimage continuous_snd)
      apply isClosed_imp (isOpen_lt continuous_fst continuous_snd)
      exact isClosed_eq hc (continuous_snd.sub continuous_fst)
    · intro s t hs ht hst
      simpa only [realArray_coe d hu] using hz s t hs ht hst
  apply hx
  refine ⟨r,hr,?_⟩
  intro s hs t ht
  rw [one_mul]
  rcases lt_trichotomy s t with hst|hst|hst
  · rw [abs_of_pos (sub_pos.mpr hst)]
    exact hall s t hs ht hst
  · subst t; rw [realArray_self d hu,sub_self,abs_zero]
  · rw [realArray_symm d hu,abs_of_neg (sub_neg.mpr hst),hall t s ht hs hst]
    ring
end StandardMapEntropy

end OAI
