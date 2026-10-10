import Mathlib
import OAI.Analysis.CoulombRadii.Packets.RadialRMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def annularAddbackKernel (h u : ℝ) (z : Space) : ℝ :=
  (5000/u)*{v : Space | h≤‖v‖ ∧ ‖v‖<8*u}.indicator (fun _ => (1:ℝ)) z+
    2*radialTailKernel (8*u) z
lemma measurableSet_addbackBand (h u : ℝ) : MeasurableSet {v : Space | h≤‖v‖ ∧ ‖v‖<8*u} :=
  (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
lemma annularAddbackKernel_measurable (h u : ℝ) : Measurable (annularAddbackKernel h u) :=
  (measurable_const.mul (measurable_const.indicator (measurableSet_addbackBand h u))).add
    (measurable_const.mul (radialTailKernel_measurable _))
lemma annularAddbackKernel_nonneg {u : ℝ} (hu : 0<u) (h : ℝ) (z : Space) :
    0≤annularAddbackKernel h u z := by
  exact add_nonneg (mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
    (mul_nonneg (by norm_num) (radialTailKernel_nonneg _ _))
lemma annularAddbackKernel_bound {u : ℝ} (hu : 0<u) (h : ℝ) (z : Space) :
    annularAddbackKernel h u z≤5001/u := by
  have hb : {v : Space | h≤‖v‖ ∧ ‖v‖<8*u}.indicator (fun _ => (1:ℝ)) z≤1 := by
    by_cases hz : h≤‖z‖ ∧ ‖z‖<8*u <;> simp [hz]
  have ht := radialTailKernel_le (show 0<8*u by positivity) z
  have H := add_le_add (mul_le_mul_of_nonneg_left hb (show 0≤5000/u by positivity))
    (mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤2 by norm_num))
  apply H.trans
  rw [mul_one]
  have he : 5000/u+2*(8*u)⁻¹=(5000+1/4)/u := by ring
  rw [he]
  exact div_le_div_of_nonneg_right (by norm_num) hu.le

lemma innerBall_subset_far {u h : ℝ} (hu : 0<u) (hh : h≤u/4) {y : Space} (hy : u/2≤‖y‖) :
    Metric.ball (0:Space) h ⊆ {z : Space | 40*atomicCellScale y≤‖z-y‖} := by
  intro z hz
  have hn : ‖z‖<h := by simpa only [Metric.mem_ball,dist_zero_right] using hz
  have ht : ‖y‖≤‖z-y‖+‖z‖ := by simpa only [dist_eq_norm,dist_zero_right,sub_zero,norm_sub_rev] using dist_triangle y z 0
  change 40*(‖y‖/100000) ≤ ‖z-y‖
  linarith

lemma annularAddbackKernel_coulomb {u h : ℝ} (hu : 0<u) {y z : Space}
    (hylo : u/2≤‖y‖) (hyhi : ‖y‖≤4*u) (hz : h≤‖z‖)
    (hfar : 40*atomicCellScale y≤‖z-y‖) :
    coulombKernel (z-y)≤annularAddbackKernel h u z := by
  by_cases hzu : ‖z‖<8*u
  · have hd : u/5000≤‖z-y‖ := by dsimp only [atomicCellScale] at hfar; linarith
    have H : coulombKernel (z-y)≤5000/u := by
      unfold coulombKernel
      apply (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0<u/5000) hd) (by positivity : 0<u/5000)).2 at hd
      simpa using hd
    unfold annularAddbackKernel
    rw [indicator_of_mem (show z∈{v : Space | h≤‖v‖ ∧ ‖v‖<8*u} from ⟨hz,hzu⟩),mul_one]
    exact H.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) (radialTailKernel_nonneg _ _)))
  · have hn : 8*u≤‖z‖ := le_of_not_gt hzu
    have hz0 : 0<‖z‖ := lt_of_lt_of_le (by positivity) hn
    have ht : ‖z‖≤‖z-y‖+‖y‖ := by simpa only [dist_eq_norm,dist_zero_right,sub_zero] using dist_triangle z y 0
    have hd : ‖z‖/2≤‖z-y‖ := by linarith
    have H : coulombKernel (z-y)≤2*‖z‖⁻¹ := by
      unfold coulombKernel
      have HH := (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0<‖z‖/2) hd) (by positivity : 0<‖z‖/2)).2 hd
      simpa [div_eq_mul_inv] using HH
    unfold annularAddbackKernel radialTailKernel
    rw [ite_eq_left hn,indicator_of_notMem (show z∉{v : Space | h≤‖v‖ ∧ ‖v‖<8*u} from fun h => hzu h.2),mul_zero,zero_add]
    exact H

lemma rawInnerField_addback {n : ℕ} {u h : ℝ} (hu : 0<u) (hh : h≤u/4) (V : ℝ)
    {y : Space} (hylo : u/2≤‖y‖) (hyhi : ‖y‖≤4*u) (x : Configuration n) :
    rawSignedField V (Metric.ball 0 h) y x ≤
      rawSignedField V {z : Space | 40*atomicCellScale y≤‖z-y‖} y x+
        arrayStatistic (annularAddbackKernel h u) x := by
  have H (i : Fin n) :
      (if position x i∈{z : Space | 40*atomicCellScale y≤‖z-y‖} then coulombKernel (position x i-y) else 0) ≤
        (if position x i∈Metric.ball 0 h then coulombKernel (position x i-y) else 0)+annularAddbackKernel h u (position x i) := by
    by_cases hi : position x i∈Metric.ball 0 h
    · rw [ite_eq_left hi,ite_eq_left (innerBall_subset_far hu hh hylo hi)]
      exact le_add_of_nonneg_right (annularAddbackKernel_nonneg hu h _)
    · rw [ite_eq_right hi]
      simp only [Set.mem_ofPred_eq]
      by_cases hf : 40*atomicCellScale y≤‖position x i-y‖
      · rw [ite_eq_left hf,zero_add]
        exact annularAddbackKernel_coulomb hu hylo hyhi
          (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hi) hf
      · rw [ite_eq_right hf,zero_add]
        exact annularAddbackKernel_nonneg hu h _
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => H i)
  simp only [Finset.sum_add_distrib] at HH
  unfold rawSignedField restrictedOutPotential arrayStatistic
  linarith

lemma rawRMS_annularAddback {n : ℕ} (ψ : H1Vector n) {u : ℝ} (hu : 0<u) (h : ℝ) :
    rawRMS ψ (arrayStatistic (annularAddbackKernel h u)) ≤
      (5000/u)*Real.sqrt (localCountSecondMoment ψ {v : Space | h≤‖v‖ ∧ ‖v‖<8*u})+
        2*rawRMS ψ (arrayStatistic (radialTailKernel (8*u))) := by
  have he : arrayStatistic (annularAddbackKernel h u)=(fun x : Configuration n =>
      (5000/u)*localCount {v : Space | h≤‖v‖ ∧ ‖v‖<8*u} x+2*arrayStatistic (radialTailKernel (8*u)) x) := by
    funext x
    simp only [arrayStatistic,annularAddbackKernel,Finset.sum_add_distrib,←Finset.mul_sum,localCount]
  rw [he]
  have hb (x : Configuration n) : |(5000/u)*localCount {v : Space | h≤‖v‖ ∧ ‖v‖<8*u} x|≤(5000/u)*(n:ℝ) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤5000/u),abs_of_nonneg (localCount_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (localCount_le _ _) (by positivity)
  have ht (x : Configuration n) : |2*arrayStatistic (radialTailKernel (8*u)) x|≤2*((n:ℝ)/(8*u)) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_left (radialTailStatistic_bound (by positivity) x) (by norm_num)
  exact (rawRMS_add ψ _ _ (measurable_const.mul (localCount_measurable (measurableSet_addbackBand h u)))
    (measurable_const.mul (arrayStatistic_measurable (radialTailKernel_measurable _))) hb ht).trans_eq (by
      change rawRMS ψ (fun x => (5000/u)*localCount {v : Space | h≤‖v‖ ∧ ‖v‖<8*u} x)+
        rawRMS ψ (fun x => 2*arrayStatistic (radialTailKernel (8*u)) x) = _
      rw [rawRMS_const_mul ψ _ (by positivity),rawRMS_const_mul ψ _ (by norm_num)]
      rfl)

lemma screenMass_zero_mono {h r : ℝ} (hh : 0<h) (hr : h≤r) : screenMass 0 r ≤ screenMass 0 h := by
  simp only [screenMass,zero_mul,Real.sqrt_zero,add_zero,screenBaseMass]
  apply max_le_max _ le_rfl
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hh.le hr 3)

lemma dyadic_annulus_cover {h : ℝ} (hh : 0<h) (N : ℕ) :
    {z : Space | h≤‖z‖ ∧ ‖z‖<(2:ℝ)^N*h} ⊆
      ⋃ j : Fin N, {z : Space | (1/2:ℝ)*((2:ℝ)^j.val*h)<‖z‖ ∧ ‖z‖<4*((2:ℝ)^j.val*h)} := by
  induction N with
  | zero => intro z hz; simp only [pow_zero,one_mul] at hz; exact (not_lt_of_ge hz.1 hz.2).elim
  | succ N ih =>
    intro z hz
    by_cases ht : ‖z‖<(2:ℝ)^N*h
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (ih ⟨hz.1,ht⟩)
      exact Set.mem_iUnion.mpr ⟨j.castSucc,hj⟩
    · refine Set.mem_iUnion.mpr ⟨Fin.last N,?_⟩
      have hr : 0<(2:ℝ)^N*h := by positivity
      have H := hz.2
      simp only [pow_succ] at H
      constructor <;> simp only [Fin.val_last] <;> nlinarith [le_of_not_gt ht]

theorem atomic_dyadic_count_RMS : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {h : ℝ}, 0<h → ∀ N : ℕ,
      Real.sqrt (localCountSecondMoment ψ {z : Space | h≤‖z‖ ∧ ‖z‖<(2:ℝ)^N*h}) ≤
        C*N*screenMass 0 h := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=(1/2:ℝ)) (β:=4) (by norm_num) (by norm_num)
  refine ⟨Real.sqrt C,Real.sqrt_nonneg _,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate h hh N
  let A : Fin N → Set Space := fun j => {z | (1/2:ℝ)*((2:ℝ)^j.val*h)<‖z‖ ∧ ‖z‖<4*((2:ℝ)^j.val*h)}
  have hA (j) : MeasurableSet (A j) :=
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hc (j : Fin N) : localCountSecondMoment ψ (A j)≤C*(screenMass 0 h)^2 := by
    have hr : 0<(2:ℝ)^j.val*h := by positivity
    have hs : h≤(2:ℝ)^j.val*h := by nlinarith [(one_le_pow₀ (n:=j.val) (show (1:ℝ)≤2 by norm_num))]
    have HH := H S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate) (le_refl 0) hr
    exact HH.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (screenMass_pos _ _).le (screenMass_zero_mono hh hs) 2) hC)
  have HC := (localCountSecondMoment_cover ψ A hA (dyadic_annulus_cover hh N)).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hc j)) (by positivity))
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity [screenMass_pos 0 h],?_⟩
  apply HC.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_pow,Real.sq_sqrt hC]
  ring

end Coulomb
end

end

end OAI
