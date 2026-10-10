import Mathlib
import OAI.Probability.SKBarriers.Dynamics.HeatBathChoice
import OAI.Probability.SKBarriers.Dynamics.HeatBathEnergy

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem update_reversible {n : ℕ} (x y : Config n) (i : Fin n)
    (h : Function.update x i (y i) = y) : Function.update y i (x i) = x := by
  classical
  funext j
  by_cases hj : j=i
  · subst j; simp
  · have H := congrFun h j
    simpa only [Function.update_of_ne hj] using H.symm

theorem siteChoice_detailedBalance {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) (i : Fin n)
    (h : Function.update x i (y i) = y) :
    gibbs β J x*siteChoice β J x i (y i) = gibbs β J y*siteChoice β J y i (x i) := by
  have hF : localField J y i = localField J x i := by
    rw [← h]
    exact localField_update J x i (y i)
  have hH : hamiltonian J y = hamiltonian J x+(spin (y i)-spin (x i))*localField J x i := by
    simpa only [h] using hamiltonian_update J x i (y i)
  have he : Real.exp (β*hamiltonian J x)*Real.exp (β*spin (y i)*localField J x i) =
      Real.exp (β*hamiltonian J y)*Real.exp (β*spin (x i)*localField J x i) := by
    rw [← Real.exp_add,← Real.exp_add,hH]
    congr 1
    ring
  unfold gibbs siteChoice
  rw [hF,div_mul_div_comm,div_mul_div_comm,he]

theorem heatBath_detailedBalance {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    gibbs β J x*heatBath β J x y = gibbs β J y*heatBath β J y x := by
  classical
  unfold heatBath
  rw [← mul_div_assoc,← mul_div_assoc,Finset.mul_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Function.update x i (y i) = y
  · have hr := update_reversible x y i h
    simp only [ite_eq_left h,ite_eq_left hr]
    exact siteChoice_detailedBalance β J x y i h
  · have hr : Function.update y i (x i) ≠ x := fun hy => h (update_reversible y x i hy)
    simp only [ite_eq_right h,ite_eq_right hr,mul_zero]

theorem heatBath_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (y : Config n) :
    ∑ x : Config n, gibbs β J x*heatBath β J x y = gibbs β J y := by
  simp_rw [heatBath_detailedBalance]
  rw [← Finset.mul_sum,heatBath_sum hn,mul_one]

theorem discreteKernel_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (k : ℕ) (y : Config n) : ∑ x : Config n, gibbs β J x*discreteKernel β J k x y = gibbs β J y := by
  classical
  induction k with
  | zero => simp [discreteKernel]
  | succ k ih =>
    simp only [discreteKernel,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc,← Finset.sum_mul,heatBath_stationary hn]
    exact ih

theorem overlap_update_le {n : ℕ} (hn : 0 < n) (v x : Config n) (i : Fin n) (b : Bool) :
    |overlap v (Function.update x i b)-overlap v x| ≤ 2/(n:ℝ) := by
  classical
  have H : (∑ j : Fin n, spin (v j)*spin (Function.update x i b j)) =
      (∑ j : Fin n, spin (v j)*spin (x j))+spin (v i)*(spin b-spin (x i)) := by
    have ht (j : Fin n) : spin (v j)*spin (Function.update x i b j) =
        spin (v j)*spin (x j)+(if j=i then spin (v i)*(spin b-spin (x i)) else 0) := by
      by_cases hj : j=i
      · subst j; simp only [Function.update_self,ite_true]; ring
      · simp only [Function.update_of_ne hj,ite_eq_right hj,add_zero]
    simp_rw [ht]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hb : |spin (v i)*(spin b-spin (x i))| ≤ 2 := by
    cases hv : v i <;> cases hx : x i <;> cases b <;> norm_num [spin,hv,hx]
  unfold overlap
  rw [H,add_div,add_sub_cancel_left,abs_div,abs_of_pos (show 0 < (n:ℝ) by exact_mod_cast hn)]
  exact div_le_div_of_nonneg_right hb (by positivity)

theorem heatBath_overlap_step {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (v x y : Config n)
    (hxy : 0 < heatBath β J x y) : |overlap v y-overlap v x| ≤ 2/(n:ℝ) := by
  classical
  by_contra h
  have hz : heatBath β J x y = 0 := by
    unfold heatBath
    have HH : ∀ i : Fin n, Function.update x i (y i) ≠ y := by
      intro i hi
      exact h (hi ▸ overlap_update_le hn v x i (y i))
    simp only [HH,ite_false,Finset.sum_const_zero,zero_div]
  linarith

end SK.Analytic

end
end

end

end OAI
