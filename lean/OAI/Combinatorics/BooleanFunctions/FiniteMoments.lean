import OAI.Combinatorics.BooleanFunctions.Blocks

namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

attribute [local instance] Classical.propDecidable

namespace FiniteMoments
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem average_normalized_weight (w : α → ℝ) (hw : average w ≠ 0) :
    average (fun x => w x / average w) = 1 := by
  simp only [div_eq_mul_inv,average_mul_const,mul_inv_cancel₀ hw]

theorem normalized_product_eval (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (j : ι) (g : α → ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*g (x j)) = average (fun a => r j a*g a) := by
  have he : (fun x : ι → α => (∏ i, r i (x i))*g (x j)) =
      fun x => ∏ i, (if i = j then r i (x i)*g (x i) else r i (x i)) := by
    funext x
    have hi (i : ι) : (if i = j then r i (x i)*g (x i) else r i (x i)) =
        r i (x i)*(if i = j then g (x i) else 1) := by split_ifs <;> simp
    simp_rw [hi]
    rw [Finset.prod_mul_distrib]
    simp
  rw [he,average_pi_prod (fun i a => if i = j then r i a*g a else r i a)]
  have hf (i : ι) : average (fun a => if i = j then r i a*g a else r i a) =
      if i = j then average (fun a => r i a*g a) else 1 := by split_ifs <;> simp_all
  simp_rw [hf]
  simp

theorem normalized_product_two_eval (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (j k : ι) (hjk : j ≠ k) (g h : α → ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*g (x j)*h (x k)) =
      average (fun a => r j a*g a) * average (fun a => r k a*h a) := by
  have he : (fun x : ι → α => (∏ i, r i (x i))*g (x j)*h (x k)) =
      fun x => ∏ i, r i (x i)*(if i = j then g (x i) else 1)*(if i = k then h (x i) else 1) := by
    funext x
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    simp
  rw [he,average_pi_prod (fun i a => r i a*(if i = j then g a else 1)*(if i = k then h a else 1))]
  have hf (i : ι) : average (fun a => r i a*(if i = j then g a else 1)*(if i = k then h a else 1)) =
      (if i = j then average (fun a => r j a*g a) else 1)*
        (if i = k then average (fun a => r k a*h a) else 1) := by
    by_cases hj : i = j
    · subst i; simp [hjk]
    by_cases hk : i = k
    · subst i; simp [hj]
    simp [hj,hk,hr]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp

theorem normalized_product_sum (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (T : ι → α → ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*(∑ i, T i (x i))) =
      ∑ i, average (fun a => r i a*T i a) := by
  simp_rw [Finset.mul_sum]
  rw [average_sum]
  exact Finset.sum_congr rfl (fun _ _ => normalized_product_eval r hr _ _)

theorem normalized_product_centered_sq (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (T : ι → α → ℝ) (hT : ∀ i, average (fun a => r i a*T i a) = 0) :
    average (fun x : ι → α => (∏ i, r i (x i))*(∑ i, T i (x i))^2) =
      ∑ i, average (fun a => r i a*(T i a)^2) := by
  have he : (fun x : ι → α => (∏ i, r i (x i))*(∑ i, T i (x i))^2) =
      fun x => ∑ i, ∑ j, (∏ k, r k (x k))*T i (x i)*T j (x j) := by
    funext x
    simp only [sq,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [he,average_sum]
  simp_rw [average_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · have he' : (fun x : ι → α => (∏ k, r k (x k))*T i (x i)*T i (x i)) =
        fun x => (∏ k, r k (x k))*(T i (x i))^2 := by funext x; ring
    rw [he',normalized_product_eval r hr i (fun a => (T i a)^2)]
  · intro j _ hij
    rw [normalized_product_two_eval r hr i j (Ne.symm hij),hT,hT,mul_zero]
  · simp

theorem normalized_product_shifted_sq (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (T : ι → α → ℝ) (μ : ι → ℝ) (hμ : ∀ i, average (fun a => r i a*T i a) = μ i)
    (c : ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*(c+∑ i, T i (x i))^2) =
      (c+∑ i, μ i)^2 + ∑ i, (average (fun a => r i a*(T i a)^2)-(μ i)^2) := by
  have hc (i : ι) : average (fun a => r i a*(T i a-μ i)) = 0 := by
    simp only [mul_sub,average_sub,average_mul_const,hμ,hr,one_mul,sub_self]
  have hfirst := normalized_product_sum r hr (fun i a => T i a-μ i)
  simp only [hc,Finset.sum_const_zero] at hfirst
  have hsecond := normalized_product_centered_sq r hr (fun i a => T i a-μ i) hc
  have hp : average (fun x : ι → α => ∏ i, r i (x i)) = 1 := by rw [average_pi_prod]; simp [hr]
  have he : (fun x : ι → α => (∏ i, r i (x i))*(c+∑ i, T i (x i))^2) =
      fun x => (∏ i, r i (x i))*(∑ i, (T i (x i)-μ i))^2 +
        2*(c+∑ i, μ i)*((∏ i, r i (x i))*(∑ i, (T i (x i)-μ i))) +
        (c+∑ i, μ i)^2*(∏ i, r i (x i)) := by
    funext x; rw [Finset.sum_sub_distrib]; ring
  rw [he,average_add,average_add,average_const_mul,average_const_mul,hfirst,hsecond,hp]
  have hd (i : ι) : average (fun a => r i a*(T i a-μ i)^2) =
      average (fun a => r i a*(T i a)^2)-(μ i)^2 := by
    have he' : (fun a => r i a*(T i a-μ i)^2) =
        fun a => r i a*(T i a)^2-2*μ i*(r i a*T i a)+(μ i)^2*r i a := by funext a; ring
    rw [he',average_add,average_sub,average_const_mul,average_const_mul,hμ,hr]
    ring
  simp_rw [hd]
  ring

end FiniteMoments
end SquareRootDegree

end

end OAI
