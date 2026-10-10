import Mathlib
import OAI.Probability.SKBarriers.Dynamics.ContinuousCrossing

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def discreteMixedMass {n : ℕ} (β : ℝ) (J : Disorder n) (k : ℕ) : ℝ :=
  ∑x : Config n,if discreteDistance β J x k≤(1/4:ℝ) then gibbs β J x else 0

def continuousMixedMass {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ) : ℝ :=
  ∑x : Config n,if continuousDistance β J x t≤(1/4:ℝ) then gibbs β J x else 0

theorem discreteMixedMass_le_sign {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (k : ℕ)
    (v : Config n → Config n) : discreteMixedMass β J k ≤
      4*∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x := by
  unfold discreteMixedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : discreteDistance β J x k≤(1/4:ℝ)
  · simp only [ite_eq_left h]
    have H := discrete_sign_mass_of_tv hn β J x (v x) k h
    change (1/4:ℝ)≤kernelEvent β J (fun y => overlap (v x) y≤0) k x at H
    have := mul_le_mul_of_nonneg_left H (gibbs_pos β J x).le
    linarith only [this]
  · simp only [ite_eq_right h]
    exact mul_nonneg (by norm_num) (mul_nonneg (gibbs_pos β J x).le (kernelEvent_nonneg _ _ _ _ _))

theorem continuousMixedMass_le_sign {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0≤t)
    (v : Config n → Config n) : continuousMixedMass β J t ≤
      4*∑x,gibbs β J x*∑y,if overlap (v x) y≤0 then continuousKernel β J t x y else 0 := by
  unfold continuousMixedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : continuousDistance β J x t≤(1/4:ℝ)
  · simp only [ite_eq_left h]
    have H := continuous_sign_mass_of_tv hn β J x (v x) ht h
    have := mul_le_mul_of_nonneg_left H (gibbs_pos β J x).le
    linarith only [this]
  · simp only [ite_eq_right h]
    apply mul_nonneg (by norm_num)
    apply mul_nonneg (gibbs_pos β J x).le
    apply Finset.sum_nonneg
    intro y _
    split_ifs
    · exact continuousKernel_nonneg β J ht x y
    · exact le_rfl

theorem averaged_sign_clock {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0≤t)
    (v : Config n → Config n) :
    (∑x,gibbs β J x*∑y,if overlap (v x) y≤0 then continuousKernel β J t x y else 0)=
      ∑' k : ℕ,clockWeight ((n:ℝ)*t) k*(∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x) := by
  simp_rw [continuous_event_eq_clock hn β J _ ht]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun x (_ : x∈(Finset.univ : Finset (Config n))) =>
    (clock_kernelEvent_summable hn β J (fun y => overlap (v x) y≤0) (by positivity) x).mul_left (gibbs β J x))]
  congr 1
  funext k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

 theorem averaged_kernelEvent_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Config n → Prop) (k : ℕ) :
    0≤∑x,gibbs β J x*kernelEvent β J (A x) k x := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (gibbs_pos β J x).le (kernelEvent_nonneg _ _ _ _ _)

 theorem averaged_kernelEvent_le_one {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (A : Config n → Config n → Prop) (k : ℕ) :
    (∑x,gibbs β J x*kernelEvent β J (A x) k x)≤1 := by
  rw [← gibbs_sum β J]
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_of_le_one_right (gibbs_pos β J x).le (kernelEvent_le_one hn β J _ _ _)

theorem averaged_sign_clock_bound {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0≤t)
    (v : Config n → Config n) (m : ℕ) {E : ℝ} (hE : 0≤E)
    (h : ∀k ≤ m,(∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x)≤E) :
    (∑x,gibbs β J x*∑y,if overlap (v x) y≤0 then continuousKernel β J t x y else 0)≤
      E+∑' k : ℕ,if m<k then clockWeight ((n:ℝ)*t) k else 0 := by
  rw [averaged_sign_clock hn β J ht v]
  have ha : 0≤(n:ℝ)*t := by positivity
  have hs : Summable (fun k : ℕ => clockWeight ((n:ℝ)*t) k*
      (∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x)) := by
    apply Summable.of_nonneg_of_le _ _ (clockWeight_hasSum ((n:ℝ)*t)).summable
    · intro k; exact mul_nonneg (clockWeight_nonneg ha k) (averaged_kernelEvent_nonneg _ _ _ _)
    · intro k; exact mul_le_of_le_one_right (clockWeight_nonneg ha k) (averaged_kernelEvent_le_one hn _ _ _ _)
  have HB := hs.tsum_le_tsum (g := fun k => clockWeight ((n:ℝ)*t) k*E+(if m<k then clockWeight ((n:ℝ)*t) k else 0))
    (fun k => by
      by_cases hk : m<k
      · simp only [ite_eq_left hk]
        have H := mul_le_of_le_one_right (clockWeight_nonneg ha k) (averaged_kernelEvent_le_one hn β J (fun x y => overlap (v x) y≤0) k)
        linarith only [H,mul_nonneg (clockWeight_nonneg ha k) hE]
      · simp only [ite_eq_right hk,add_zero]
        exact mul_le_mul_of_nonneg_left (h k (le_of_not_gt hk)) (clockWeight_nonneg ha k))
    (((clockWeight_hasSum ((n:ℝ)*t)).summable.mul_right E).add (clockWeight_tail_summable ha m))
  simpa only [Summable.tsum_add ((clockWeight_hasSum ((n:ℝ)*t)).summable.mul_right E) (clockWeight_tail_summable ha m),tsum_mul_right,clockWeight_sum,one_mul] using HB

 theorem mixedMass_bounds_of_crossing {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (L E : ℝ)
    (hL : 0≤L) (hE : 0≤E) (v : Config n → Config n)
    (h : ∀k≤⌈Real.exp (2*L)⌉₊,(∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x)≤E) :
    continuousMixedMass β J (Real.exp L)≤4*(E+(n:ℝ)*Real.exp (-L)) ∧
    discreteMixedMass β J ⌊Real.exp L⌋₊≤4*E := by
  constructor
  · refine (continuousMixedMass_le_sign hn β J (Real.exp_pos L).le v).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (averaged_sign_clock_bound hn β J (Real.exp_pos L).le v _ hE h).trans
      (add_le_add le_rfl (attempt_horizon_tail n L))
  · refine (discreteMixedMass_le_sign hn β J ⌊Real.exp L⌋₊ v).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply h
    exact (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hL]))).trans (Nat.floor_le_ceil _)

end SK.Analytic

end
end

end OAI
