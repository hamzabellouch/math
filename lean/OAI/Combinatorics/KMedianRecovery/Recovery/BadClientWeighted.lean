import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ClassSlotsMem

namespace OAI

namespace MetricKMedianRecovery.LocalSearch

lemma bad_client_weighted {E : Type*} [Fintype E]
    (weight : E → ℝ) (add remove : E → Prop) [DecidablePred add] [DecidablePred remove] (change : E → ℝ)
    (hw : ∀ e, 0 ≤ weight e) (P S u : ℝ) (hP : 0 ≤ P)
    (hadd : (∑ e, if add e then weight e else 0) = 1)
    (hremove : (∑ e, if remove e then weight e else 0) ≤ u)
    (hchange : ∀ e, 0 < weight e → change e ≤
      (if add e then P-S else 0) + (if remove e then 2*P else 0)) :
    (∑ e, weight e * change e) ≤ (1+2*u)*P-S := by
  classical
  have hle : (∑ e, weight e*change e) ≤
      ∑ e, weight e*((if add e then P-S else 0)+(if remove e then 2*P else 0)) := by
    apply Finset.sum_le_sum
    intro e _
    rcases (hw e).eq_or_lt with he | he
    · simp only [← he,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (hchange e he) (hw e)
  have he : (∑ e, weight e*((if add e then P-S else 0)+(if remove e then 2*P else 0))) =
      (∑ e, if add e then weight e else 0)*(P-S) +
      (∑ e, if remove e then weight e else 0)*(2*P) := by
    simp_rw [mul_add,Finset.sum_add_distrib,Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro e _ <;> split_ifs <;> ring
  rw [he,hadd,one_mul] at hle
  have hh := mul_le_mul_of_nonneg_right hremove (by positivity : 0 ≤ 2*P)
  linarith

lemma good_client_weighted {E : Type*} [Fintype E]
    (weight : E → ℝ) (remove : E → Prop) [DecidablePred remove] (change : E → ℝ)
    (hw : ∀ e, 0 ≤ weight e) (P S u : ℝ) (hPS : S ≤ P)
    (hremove : (∑ e, if remove e then weight e else 0) ≤ u)
    (hchange : ∀ e, 0 < weight e → change e ≤ (if remove e then P-S else 0)) :
    (∑ e, weight e * change e) ≤ u*(P-S) := by
  classical
  calc
    (∑ e, weight e * change e) ≤ ∑ e, weight e*(if remove e then P-S else 0) := by
      apply Finset.sum_le_sum
      intro e _
      rcases (hw e).eq_or_lt with he | he
      · simp only [← he,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hchange e he) (hw e)
    _ = (∑ e, if remove e then weight e else 0)*(P-S) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    _ ≤ u*(P-S) := mul_le_mul_of_nonneg_right hremove (sub_nonneg.mpr hPS)

end MetricKMedianRecovery.LocalSearch
namespace MetricKMedianRecovery.LocalSearch
variable {V E : Type*} [PseudoMetricSpace V] [DecidableEq V] [Fintype E]

lemma bad_routing_change (S R A : Finset V) (hS : S.Nonempty) (p i : V)
    (hpreserve : i ∉ A → nearest S hS i ∉ R) :
    connection ((S \ R) ∪ A) p - connection S p ≤
      (if i ∈ A then dist p i - connection S p else 0) +
      (if nearest S hS p ∈ R then 2*dist p i else 0) := by
  by_cases hi : i ∈ A
  · have hc := connection_le (p := p) (Finset.mem_union_right (S \ R) hi)
    simp only [hi,ite_true]
    split_ifs <;> nlinarith [dist_nonneg (x := p) (y := i)]
  · simp only [hi,ite_false,zero_add]
    by_cases hp : nearest S hS p ∈ R
    · simp only [hp,ite_true]
      have hmem : nearest S hS i ∈ (S \ R) ∪ A := Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨nearest_mem S hS i,hpreserve hi⟩)
      have hc := connection_le (p := p) hmem
      have hnear : dist i (nearest S hS i) ≤ dist i (nearest S hS p) := by
        rw [nearest_distance]
        exact connection_le (nearest_mem S hS p)
      have ht1 := dist_triangle p i (nearest S hS i)
      have ht2 := dist_triangle i p (nearest S hS p)
      rw [dist_comm i p,nearest_distance] at ht2
      linarith
    · simp only [hp,ite_false]
      have hc := connection_le (p := p) (Finset.mem_union_left A
        (Finset.mem_sdiff.mpr ⟨nearest_mem S hS p,hp⟩))
      rw [nearest_distance] at hc
      linarith

lemma good_routing_change (S R A : Finset V) (hS : S.Nonempty) (p proxy : V)
    (hproxy : proxy ∈ S) (hkeep : proxy ∉ R) :
    connection ((S \ R) ∪ A) p - connection S p ≤
      (if nearest S hS p ∈ R then dist p proxy - connection S p else 0) := by
  by_cases hp : nearest S hS p ∈ R
  · simp only [hp,ite_true]
    exact sub_le_sub_right (connection_le (p := p) (Finset.mem_union_left A
      (Finset.mem_sdiff.mpr ⟨hproxy,hkeep⟩))) _
  · simp only [hp,ite_false]
    have hc := connection_le (p := p) (Finset.mem_union_left A
      (Finset.mem_sdiff.mpr ⟨nearest_mem S hS p,hp⟩))
    rw [nearest_distance] at hc
    linarith

theorem weighted_swap_family (F D S Ob Og : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (assign proxy : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ Ob ∨ assign p ∈ Og)
    (hproxy : ∀ i ∈ Og, proxy i ∈ S)
    (R A : E → Finset V) (w : E → ℝ) (u : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hwidth : ∀ e, 0 < w e → R e ⊆ S ∧ A e ⊆ F ∧ (A e).Nonempty ∧
      (A e).card ≤ (R e).card ∧ (R e).card ≤ 5 ∧ (A e).card ≤ 5)
    (hadd : ∀ i ∈ Ob, (∑ e, if i ∈ A e then w e else 0) = 1)
    (hremove : ∀ s ∈ S, (∑ e, if s ∈ R e then w e else 0) ≤ u)
    (hkeep : ∀ e, 0 < w e → ∀ i ∈ Og, proxy i ∉ R e)
    (hpreserve : ∀ e, 0 < w e → ∀ i ∈ Ob, i ∉ A e → nearest S hS i ∉ R e) :
    0 ≤ ∑ p ∈ D, if assign p ∈ Ob then (1+2*u)*dist p (assign p)-connection S p
      else u*(dist p (proxy (assign p))-connection S p) := by
  classical
  have hnon : 0 ≤ ∑ e, w e*(cost D ((S \ R e) ∪ A e)-cost D S) := by
    apply Finset.sum_nonneg
    intro e _
    rcases (hw e).eq_or_lt with he | he
    · simp only [← he,zero_mul,le_refl]
    · obtain ⟨hrs,haf,ha,hcard,hr,hac⟩ := hwidth e he
      exact mul_nonneg (hw e) (sub_nonneg.mpr (local_exchange F D S 5 hSF hlocal
        (R e) (A e) hrs haf ha hcard hr hac))
  have hsum : (∑ e, w e*(cost D ((S \ R e) ∪ A e)-cost D S)) =
      ∑ p ∈ D, ∑ e, w e*(connection ((S \ R e) ∪ A e) p-connection S p) := by
    simp only [cost,← Finset.sum_sub_distrib,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hsum] at hnon
  refine hnon.trans (Finset.sum_le_sum (fun p hp => ?_))
  by_cases hb : assign p ∈ Ob
  · simp only [hb,ite_true]
    exact bad_client_weighted w (fun e => assign p ∈ A e)
      (fun e => nearest S hS p ∈ R e) _ hw (dist p (assign p)) (connection S p) u
      dist_nonneg (hadd _ hb) (hremove _ (nearest_mem S hS p))
      (fun e he => bad_routing_change S (R e) (A e) hS p (assign p)
        (hpreserve e he _ hb))
  · simp only [hb,ite_false]
    have hg : assign p ∈ Og := (hassign p hp).resolve_left hb
    exact good_client_weighted w (fun e => nearest S hS p ∈ R e) _ hw
      (dist p (proxy (assign p))) (connection S p) u
      (connection_le (hproxy _ hg)) (hremove _ (nearest_mem S hS p))
      (fun e he => good_routing_change S (R e) (A e) hS p _ (hproxy _ hg) (hkeep e he _ hg))

lemma weighted_swap_sum_form (D S Ob : Finset V) (assign proxy : V → V) (u : ℝ)
    (h : 0 ≤ ∑ p ∈ D, if assign p ∈ Ob then (1+2*u)*dist p (assign p)-connection S p
      else u*(dist p (proxy (assign p))-connection S p)) :
    (∑ p ∈ D.filter (fun p => assign p ∈ Ob), connection S p) +
      u*(∑ p ∈ D.filter (fun p => assign p ∉ Ob), connection S p) ≤
      (1+2*u)*(∑ p ∈ D.filter (fun p => assign p ∈ Ob), dist p (assign p)) +
      u*(∑ p ∈ D.filter (fun p => assign p ∉ Ob), dist p (proxy (assign p))) := by
  have he : (∑ p ∈ D, if assign p ∈ Ob then (1+2*u)*dist p (assign p)-connection S p
      else u*(dist p (proxy (assign p))-connection S p)) =
      ((1+2*u)*(∑ p ∈ D.filter (fun p => assign p ∈ Ob), dist p (assign p)) -
        (∑ p ∈ D.filter (fun p => assign p ∈ Ob), connection S p)) +
      u*((∑ p ∈ D.filter (fun p => assign p ∉ Ob), dist p (proxy (assign p))) -
        (∑ p ∈ D.filter (fun p => assign p ∉ Ob), connection S p)) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : assign p ∈ Ob <;> simp [hp]
  rw [he] at h
  linarith
end MetricKMedianRecovery.LocalSearch

end OAI
