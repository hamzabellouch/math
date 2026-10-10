import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.WeightedInner
import OAI.Analysis.CoulombRadii.Localization.DeletionEnvelope

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma weighted_raw_inner_exterior_abs_le {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) {t h : ℝ} (ht : 0<t) (hh : h ≤ t/2)
    {w : Space → ℝ} (hw : ∀ y, |w y| ≤ 1) (hws : ∀ y, ‖y‖<t → w y=0)
    (y : Space) (x : Configuration n) :
    |w y*rawSignedField (attraction S y) (Metric.ball 0 h) y x| ≤
      totalCharge S/t+(n:ℝ)/(t/2) := by
  by_cases hy : t ≤ ‖y‖
  · have HB := rawSignedField_abs_le (attraction S y) (Metric.ball 0 h) y
      (show 0<t/2 by positivity) (inner_shell_separation ht hh hy) x
    have HA : attraction S y ≤ totalCharge S/t := attraction_le_totalCharge_div S ht y
      (fun j => by simpa only [hatom j,sub_zero] using hy)
    rw [abs_of_nonneg (attraction_nonneg S y)] at HB
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hw y) (abs_nonneg _)).trans
      (by simpa only [one_mul] using HB.trans (add_le_add HA le_rfl))
  · rw [hws y (lt_of_not_ge hy),zero_mul,abs_zero]
    exact add_nonneg (div_nonneg (totalCharge_nonneg S) ht.le) (by positivity)

lemma weightedInnerField_exterior_abs_le {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) {t h : ℝ} (ht : 0<t) (hh : h ≤ t/2)
    {w : Space → ℝ} (hw : ∀ y, |w y| ≤ 1) (hws : ∀ y, ‖y‖<t → w y=0)
    (x : Configuration n) :
    |weightedInnerField S h w x| ≤ (n:ℝ)*(totalCharge S/t+(n:ℝ)/(t/2)) := by
  unfold weightedInnerField
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    weighted_raw_inner_exterior_abs_le S hatom ht hh hw hws (position x i) x)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H

lemma potentialForm_bounded_tendsto {n : ℕ} (u : H1Vector n)
    {F : ℕ → Configuration n → ℝ} {G : Configuration n → ℝ} {B : ℝ}
    (hF : ∀ k, Measurable (F k)) (hb : ∀ k x, |F k x| ≤ B)
    (hlim : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (G x))) :
    Tendsto (fun k => potentialForm (F k) u) atTop (𝓝 (potentialForm G u)) := by
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => B*‖u.value s x‖^2)
  · intro k
    exact (hF k).aestronglyMeasurable.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)
  · exact ((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul B
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u.value s x‖)]
    exact mul_le_mul_of_nonneg_right (hb k x) (sq_nonneg _)
  · exact Eventually.of_forall (fun x => (hlim x).mul_const _)

lemma potentialForm_sum_values {n : ℕ} {ι : Type*} (u : H1Vector n)
    (s : Finset ι) (F : ι → Configuration n → ℝ)
    (hF : ∀ i∈s, ∀ q : Spins n, Integrable (fun x => F i x*‖u.value q x‖^2)) :
    potentialForm (fun x => ∑ i∈s, F i x) u=∑ i∈s, potentialForm (F i) u := by
  simp only [potentialForm,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  exact integral_finsetSum s (fun i hi => hF i hi q)

lemma weightedInnerField_sum_weights {J n : ℕ} {ι : Type*} (S : Nuclei J) (h : ℝ)
    (s : Finset ι) (w : ι → Space → ℝ) (x : Configuration n) :
    weightedInnerField S h (fun y => ∑ i∈s, w i y) x=
      ∑ i∈s, weightedInnerField S h (w i) x := by
  simp only [weightedInnerField,Finset.sum_mul]
  exact Finset.sum_comm

lemma deletionShellWeight_sum_supported {t : ℝ} (ht : 0<t) (w : Space → ℝ) (k : ℕ)
    (y : Space) (hy : ‖y‖<t) : (∑ j∈Finset.range k, deletionShellWeight t w j y)=0 := by
  rw [deletionShellWeight_sum ht]
  split_ifs with h
  · exact False.elim (not_le.mpr hy h.1)
  · rfl

lemma deletionShellWeight_sum_tendsto {t : ℝ} (ht : 0<t) {w : Space → ℝ}
    (hws : ∀ y, ‖y‖<t → w y=0) (y : Space) :
    Tendsto (fun k => ∑ j∈Finset.range k, deletionShellWeight t w j y) atTop (𝓝 (w y)) := by
  have H : Tendsto (fun k : ℕ => (2:ℝ)^k*t) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const ht
  have he := H.eventually (eventually_gt_atTop ‖y‖)
  by_cases hy : t ≤ ‖y‖
  · apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [he] with k hk
    rw [deletionShellWeight_sum ht,ite_eq_left ⟨hy,hk⟩]
  · have hy' : ‖y‖<t := lt_of_not_ge hy
    simp_rw [deletionShellWeight_sum_supported ht w _ y hy',hws y hy']
    exact tendsto_const_nhds

lemma weightedInnerField_shell_partial_tendsto {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) (u : H1Vector n) {t : ℝ} (ht : 0<t)
    {w : Space → ℝ} (hw : Measurable w) (hb : ∀ y, |w y| ≤ 1)
    (hws : ∀ y, ‖y‖<t → w y=0) :
    Tendsto (fun k => potentialForm (weightedInnerField S (t/4)
      (fun y => ∑ j∈Finset.range k, deletionShellWeight t w j y)) u)
      atTop (𝓝 (potentialForm (weightedInnerField S (t/4) w) u)) := by
  apply potentialForm_bounded_tendsto (B:=(n:ℝ)*(totalCharge S/t+(n:ℝ)/(t/2)))
  · intro k
    exact weightedInnerField_measurable S (t/4)
      (Finset.measurable_fun_sum _ (fun j _ => deletionShellWeight_measurable hw t j))
  · intro k x
    exact weightedInnerField_exterior_abs_le S hatom ht (by linarith)
      (deletionShellWeight_sum_bound ht hb k) (deletionShellWeight_sum_supported ht w k) x
  · intro x
    apply tendsto_finsetSum
    intro i hi
    exact (deletionShellWeight_sum_tendsto ht hws (position x i)).mul_const _

end Coulomb
end

end

end OAI
