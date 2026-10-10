import Mathlib
import OAI.Analysis.CoulombRadii.Packets.ScreenBox
import OAI.Analysis.CoulombRadii.Localization.ShellIMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def weightedInnerField {J n : ℕ} (S : Nuclei J) (h : ℝ) (w : Space → ℝ)
    (x : Configuration n) : ℝ :=
  ∑ i, w (position x i)*rawSignedField (attraction S (position x i)) (Metric.ball 0 h) (position x i) x

lemma weightedInnerField_measurable {J n : ℕ} (S : Nuclei J) (h : ℝ)
    {w : Space → ℝ} (hw : Measurable w) : Measurable (@weightedInnerField J n S h w) := by
  unfold weightedInnerField
  apply Finset.measurable_fun_sum
  intro i hi
  have hp : Measurable (fun x : Configuration n => position x i) :=
    (continuous_position i).measurable
  have hc : Measurable (fun x : Configuration n => (x,position x i)) :=
    measurable_id.prodMk hp
  have hr : Measurable (fun x : Configuration n =>
      restrictedOutPotential x (Metric.ball 0 h) (position x i)) :=
    (restrictedOutPotential_joint_measurable (m:=n) (A:=Metric.ball (0:Space) h) measurableSet_ball).comp (f:=fun x : Configuration n => (x,position x i)) hc
  have ha : Measurable (fun x : Configuration n => attraction S (position x i)) :=
    (attraction_measurable S).comp hp
  exact (hw.comp hp).mul (ha.sub hr)

lemma weightedInnerField_reindex {J m n : ℕ} (S : Nuclei J) (h : ℝ) (w : Space → ℝ)
    (e : Fin m ≃ Fin n) (x : Configuration m) :
    weightedInnerField S h w (reindexConfiguration e x)=weightedInnerField S h w x := by
  simp only [weightedInnerField,rawSignedField_reindex]
  change (∑ i : Fin n, w (position x (e.symm i))*
    rawSignedField (attraction S (position x (e.symm i))) (Metric.ball 0 h) (position x (e.symm i)) x)=_
  exact Equiv.sum_comp e.symm (fun i : Fin m => w (position x i)*
    rawSignedField (attraction S (position x i)) (Metric.ball 0 h) (position x i) x)

lemma inner_shell_separation {u h : ℝ} (hu : 0<u) (hh : h ≤ u/2)
    {y : Space} (hy : u ≤ ‖y‖) (z : Space) (hz : z∈Metric.ball (0:Space) h) :
    u/2 ≤ ‖z-y‖ := by
  have hn : ‖z‖<h := by simpa only [Metric.mem_ball,dist_zero_right] using hz
  have H : ‖y‖ ≤ ‖z-y‖+‖z‖ := by
    simpa only [dist_eq_norm,sub_zero,norm_sub_rev] using dist_triangle y z 0
  apply (mul_le_mul_iff_right₀ hu).mp
  exact mul_le_mul_of_nonneg_left (by linarith only [hh, hy, hn, H]) hu.le

lemma weighted_raw_inner_abs_le {J n : ℕ} (S : Nuclei J) (hatom : ∀ j, S.position j=0)
    {u h : ℝ} (hu : 0<u) (hh : h ≤ u/2) {w : Space → ℝ}
    (hw : ∀ y, |w y| ≤ 1) (hws : ∀ y∉imsShell 0 u, w y=0)
    (y : Space) (x : Configuration n) :
    |w y*rawSignedField (attraction S y) (Metric.ball 0 h) y x| ≤
      totalCharge S/u+(n:ℝ)/(u/2) := by
  by_cases hy : y∈imsShell 0 u
  · have hyr : u ≤ ‖y‖ := by simpa only [imsShell,mem_ofPred_eq,sub_zero] using hy.1
    have HB := rawSignedField_abs_le (attraction S y) (Metric.ball 0 h) y
      (show 0<u/2 by positivity) (inner_shell_separation hu hh hyr) x
    have HA : attraction S y ≤ totalCharge S/u := attraction_le_totalCharge_div S hu y
      (fun j => by simpa only [hatom j,sub_zero] using hyr)
    rw [abs_of_nonneg (attraction_nonneg S y)] at HB
    rw [abs_mul]
    calc
      _ ≤ 1*|rawSignedField (attraction S y) (Metric.ball 0 h) y x| :=
        mul_le_mul_of_nonneg_right (hw y) (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using HB.trans (add_le_add HA le_rfl)
  · rw [hws y hy,zero_mul,abs_zero]
    exact add_nonneg (div_nonneg (totalCharge_nonneg S) hu.le) (by positivity)

lemma weightedInnerField_abs_le {J n : ℕ} (S : Nuclei J) (hatom : ∀ j, S.position j=0)
    {u h : ℝ} (hu : 0<u) (hh : h ≤ u/2) {w : Space → ℝ}
    (hw : ∀ y, |w y| ≤ 1) (hws : ∀ y∉imsShell 0 u, w y=0)
    (x : Configuration n) :
    |weightedInnerField S h w x| ≤ (n:ℝ)*(totalCharge S/u+(n:ℝ)/(u/2)) := by
  unfold weightedInnerField
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => weighted_raw_inner_abs_le S hatom hu hh hw hws (position x i) x)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H

lemma weightedInnerField_join_of_support {J m k : ℕ} (S : Nuclei J) (h : ℝ)
    {u : ℝ} {w : Space → ℝ} (hws : ∀ y∉imsShell 0 u, w y=0)
    (x : Configuration m) {z : Configuration k} (hz : z∈allPositions (imsShell 0 u)ᶜ) :
    weightedInnerField S h w (joinConfiguration m k (x,z))=
      ∑ i : Fin m, w (position x i)*rawSignedField (attraction S (position x i))
        (Metric.ball 0 h) (position x i) (joinConfiguration m k (x,z)) := by
  simp only [weightedInnerField,Fin.sum_univ_add,position_join_left,position_join_right]
  have he : (∑ i : Fin k, w (position z i)*rawSignedField (attraction S (position z i))
      (Metric.ball 0 h) (position z i) (joinConfiguration m k (x,z)))=0 := by
    exact Finset.sum_eq_zero (fun i _ => by rw [hws _ (hz i),zero_mul])
  rw [he,add_zero]

lemma potentialForm_const_mul_value {n : ℕ} (v : H1Vector n) (c : ℝ) (F : Configuration n → ℝ) :
    potentialForm (fun x => c*F x) v = c*potentialForm F v := by
  simp only [potentialForm,mul_assoc,integral_const_mul,Finset.mul_sum]

lemma conditional_weighted_inner_le {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) (v : H1Vector (m+k)) {u h : ℝ}
    (hu : 0<u) (hh : h ≤ u/2) {w : Space → ℝ} (hwm : Measurable w)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1) (hws : ∀ y∉imsShell 0 u, w y=0)
    (s : Spins m) (x : Configuration m) (hm : 0 < mass (v.coreSlice s x))
    (hcore : SpatiallySupported (v.coreSlice s x).normalized (imsShell 0 u)ᶜ)
    {M : ℝ} (hM : 0 ≤ M)
    (hcap : ∀ y, u ≤ ‖y‖ → ‖y‖ ≤ 2*u →
      max (recordedFarField S (v.coreSlice s x).normalized x (Metric.ball 0 h) y) 0 ≤ M) :
    coreConditionalObservable v (weightedInnerField S h w) s x ≤ (m:ℝ)*M := by
  let v₀ := (v.coreSlice s x).normalized
  let F (i : Fin m) (z : Configuration k) := w (position x i)*rawSignedField
    (attraction S (position x i)) (Metric.ball 0 h) (position x i) (joinConfiguration m k (x,z))
  have hwabs y : |w y| ≤ 1 := by rw [abs_of_nonneg (hw0 y)]; exact hw1 y
  have hFi i : Measurable (F i) := (hwm.comp measurable_const).mul
    ((rawSignedField_measurable _ measurableSet_ball _).comp
      ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
  have hFb i z : |F i z| ≤ totalCharge S/u+((m+k:ℕ):ℝ)/(u/2) :=
    weighted_raw_inner_abs_le S hatom hu hh hwabs hws _ _
  have he : coreConditionalObservable v (weightedInnerField S h w) s x=
      ∑ i : Fin m, potentialForm (F i) v₀ := by
    unfold coreConditionalObservable potentialForm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [←integral_finsetSum _ (fun i _ => boundedObservable_integrable v₀ (F i) (hFi i) (hFb i) q)]
    apply integral_congr_ae
    filter_upwards [hcore q] with z hz
    by_cases hz' : z∈allPositions (imsShell 0 u)ᶜ
    · rw [weightedInnerField_join_of_support S h hws x hz',Finset.sum_mul]
    · rw [hz hz',norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]
      exact (Finset.sum_eq_zero (fun _ _ => mul_zero _)).symm
  rw [he]
  calc
    _ ≤ ∑ _i : Fin m, M := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hwz : w (position x i)=0
      · simp only [F,hwz,zero_mul,potentialForm,integral_zero,Finset.sum_const_zero]
        exact hM
      · have hy : position x i∈imsShell 0 u := by by_contra h; exact hwz (hws _ h)
        have hyr : u ≤ ‖position x i‖ ∧ ‖position x i‖ ≤ 2*u := by
          simpa only [imsShell,mem_ofPred_eq,sub_zero] using hy
        have hhf := coreConditionalObservable_rawSignedField v (attraction S (position x i))
          measurableSet_ball (position x i) (show 0<u/2 by positivity)
          (inner_shell_separation hu hh hyr.1) s x hm
        have heq : potentialForm (F i) v₀ = w (position x i)*
            recordedFarField S v₀ x (Metric.ball 0 h) (position x i) := by
          rw [show F i=(fun z => w (position x i)*rawSignedField (attraction S (position x i))
            (Metric.ball 0 h) (position x i) (joinConfiguration m k (x,z))) from rfl,
            potentialForm_const_mul_value]
          exact congrArg (fun z => w (position x i)*z) hhf
        rw [heq]
        exact (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (hcap _ hyr.1 hyr.2)) (hw0 _)).trans
          ((mul_le_mul_of_nonneg_right (hw1 _) hM).trans_eq (one_mul _))
    _ = _ := by simp

end Coulomb
end

end

end OAI
