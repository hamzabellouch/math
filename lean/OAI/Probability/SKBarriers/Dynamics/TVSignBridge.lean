import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic
import OAI.Probability.SKBarriers.Dynamics.HeatBathChoice

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem finite_event_le_tv {Ω : Type*} [Fintype Ω] (p q : Ω → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) (A : Ω → Prop) [DecidablePred A] :
    (∑ x, if A x then q x else 0)-(∑ x, if A x then p x else 0) ≤
      (1/2:ℝ)*∑ x, |p x-q x| := by
  have hsum : ∑ x, (q x-p x) = 0 := by rw [Finset.sum_sub_distrib,hq,hp,sub_self]
  have ht (x : Ω) : 2*(if A x then q x-p x else 0)-(q x-p x) ≤ |q x-p x| := by
    by_cases hx : A x
    · simp only [ite_eq_left hx]
      linarith [le_abs_self (q x-p x)]
    · simp only [ite_eq_right hx,mul_zero,zero_sub]
      exact neg_le_abs (q x-p x)
  have H := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Ω)) => ht x)
  have he : (∑ x, if A x then q x-p x else 0) =
      (∑ x, if A x then q x else 0)-(∑ x, if A x then p x else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,hsum,sub_zero,he] at H
  have ha : (∑ x, |q x-p x|) = ∑ x, |p x-q x| := by
    apply Finset.sum_congr rfl
    intro x _
    exact abs_sub_comm _ _
  rw [ha] at H
  linarith

theorem gibbs_nonpositive_overlap_mass {n : ℕ} (β : ℝ) (J : Disorder n) (v : Config n) :
    (1/2:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then gibbs β J y else 0 := by
  classical
  let e : Config n ≃ Config n := ⟨flip,flip,flip_flip,flip_flip⟩
  have he : (∑ y : Config n, if -overlap v y ≤ 0 then gibbs β J y else 0) =
      ∑ y : Config n, if overlap v y ≤ 0 then gibbs β J y else 0 := by
    calc
      _ = ∑ y : Config n, if overlap v (e y) ≤ 0 then gibbs β J (e y) else 0 := by
        change _ = ∑ y : Config n, if overlap v (flip y) ≤ 0 then gibbs β J (flip y) else 0
        simp only [overlap_flip_right,gibbs_flip]
      _ = _ := Equiv.sum_comp e (fun y => if overlap v y ≤ 0 then gibbs β J y else 0)
  have ht (y : Config n) : gibbs β J y ≤
      (if overlap v y ≤ 0 then gibbs β J y else 0)+
      (if -overlap v y ≤ 0 then gibbs β J y else 0) := by
    by_cases h : overlap v y ≤ 0
    · simp only [ite_eq_left h]
      split_ifs <;> linarith [gibbs_pos β J y]
    · have h' : -overlap v y ≤ 0 := by linarith [lt_of_not_ge h]
      simp only [ite_eq_right h,ite_eq_left h',zero_add,le_refl]
  have H := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) => ht y)
  rw [gibbs_sum,Finset.sum_add_distrib,he] at H
  linarith

theorem discrete_sign_mass_of_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (x v : Config n) (k : ℕ) (hTV : discreteDistance β J x k ≤ (1/4:ℝ)) :
    (1/4:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then discreteKernel β J k x y else 0 := by
  have H := finite_event_le_tv (discreteKernel β J k x) (gibbs β J)
    (discreteKernel_sum hn β J k x) (gibbs_sum β J) (fun y => overlap v y ≤ 0)
  have HG := gibbs_nonpositive_overlap_mass β J v
  change _ ≤ discreteDistance β J x k at H
  linarith

end SK.Analytic

end
end

end

end OAI
