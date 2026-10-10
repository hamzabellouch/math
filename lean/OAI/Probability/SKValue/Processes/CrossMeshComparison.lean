import Mathlib
import OAI.Probability.SKValue.Processes.CrossMesh

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def ordinaryMeshSource (T : ℝ) (N : ℕ) (γ β : ℝ → ℝ) (V : ℝ → ℝ → ℝ) : ℝ :=
  stepSize T N*∑ j : Fin N,(β (meshTime T N j)-γ (meshTime T N j))*
    (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j))
      (euler T N γ (fun t ↦ deriv (V t)) z j))^2 ∂gaussianProduct (Fin (N+1)))

lemma crossMeshSource_half_form (T : ℝ) (N : ℕ) (γ β : ℝ → ℝ) (V U : ℝ → ℝ → ℝ) :
    crossMeshSource T N γ β V U=stepSize T N*∑ j : Fin N,(β (meshTime T N j)-γ (meshTime T N j))*
      (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j))
        (euler T N β (crossFeedback V U) z j))^2 ∂gaussianProduct (Fin (N+1))) := by
  unfold crossMeshSource
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ (β (meshTime T N j)-γ (meshTime T N j))*
    (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j))
      (euler T N β (crossFeedback V U) z j))^2 ∂gaussianProduct (Fin (N+1))))]
  simp only [integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma crossMeshSource_difference_bound {T K L K' L' d R : ℝ}
    {γ β : ℝ → ℝ} {V U : ℝ → ℝ → ℝ}
    (hV : ValueStrip T γ V K L) (hU : ValueStrip T β U K' L')
    (hT : 0≤T) {N : ℕ} (hN : 0<N) (hd : 0≤d) (hR : 0≤R)
    (hc : ∀ t∈Icc (0 : ℝ) T,|β t-γ t|≤d)
    (hY : ∀ z : Fin (N+1) → ℝ,∀ j≤N,
      |euler T N β (crossFeedback V U) z j-euler T N γ (fun t ↦ deriv (V t)) z j|≤R) :
    |crossMeshSource T N γ β V U-ordinaryMeshSource T N γ β V|≤T*d*L*R := by
  have hδ : 0 ≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg _)
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT hN hj
  have hfm (j : ℕ) (hj : j<N) : Measurable (crossFeedback V U (meshTime T N j)) :=
    (((hU.smooth _ (htime j hj.le)).continuous_deriv (by norm_num)).measurable.add
      ((hV.smooth _ (htime j hj.le)).continuous_deriv (by norm_num)).measurable).div_const 2
  have hfb (j : ℕ) (hj : j<N) (x : ℝ) : |crossFeedback V U (meshTime T N j) x|≤1 :=
    crossFeedback_bound (hV.bounded _ (htime j hj.le) x) (hU.bounded _ (htime j hj.le) x)
  have hm (j : Fin N) :
      |(∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N β (crossFeedback V U) z j))^2
        ∂gaussianProduct (Fin (N+1)))-
       (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2
        ∂gaussianProduct (Fin (N+1)))|≤L*R := by
    have hLip := hV.product_lipschitzWith (htime j j.isLt.le)
    have hM1 := lipschitz_comp_memLp_finite hLip (euler_memLp T N β (crossFeedback V U) hfm hfb j j.isLt.le)
    have hM2 := lipschitz_comp_memLp_finite hLip (euler_memLp T N γ (fun t ↦ deriv (V t))
      (fun k hk ↦ ((hV.smooth _ (htime k hk.le)).continuous_deriv (by norm_num)).measurable)
      (fun k hk x ↦ hV.bounded _ (htime k hk.le) x) j j.isLt.le)
    rw [←integral_sub (f := fun z ↦ (1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N β (crossFeedback V U) z j))^2)
      (g := fun z ↦ (1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2)
      (hM1.integrable (by norm_num)) (hM2.integrable (by norm_num))]
    apply (abs_integral_le_integral_abs).trans
    calc
      _ ≤ ∫ _ : Fin (N+1) → ℝ,|L*R| ∂gaussianProduct (Fin (N+1)) := by
        apply integral_mono ((hM1.integrable (by norm_num)).sub (hM2.integrable (by norm_num))).norm (integrable_const _)
        intro z
        have hh := hLip.dist_le_mul (euler T N β (crossFeedback V U) z j) (euler T N γ (fun t ↦ deriv (V t)) z j)
        rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ hV.L_nonneg] at hh
        exact (hh.trans (mul_le_mul_of_nonneg_left (hY z j j.isLt.le) hV.L_nonneg)).trans
          (le_abs_self (L*R))
      _=L*R := by simp [abs_of_nonneg (mul_nonneg hV.L_nonneg hR)]
  rw [crossMeshSource_half_form,ordinaryMeshSource,←mul_sub,←Finset.sum_sub_distrib,
    abs_mul,abs_of_nonneg hδ]
  calc
    _ ≤ stepSize T N*∑ j : Fin N,|(β (meshTime T N j)-γ (meshTime T N j))*
      ((∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N β (crossFeedback V U) z j))^2 ∂gaussianProduct (Fin (N+1)))-
       (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2 ∂gaussianProduct (Fin (N+1))))| := by
      simp_rw [←mul_sub]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hδ
    _ ≤ stepSize T N*∑ _ : Fin N,d*(L*R) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hc _ (htime j j.isLt.le)) (hm j) (abs_nonneg _) hd
    _=T*d*L*R := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,stepSize]
      field_simp

end SKValue

end

end OAI
