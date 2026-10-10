import OAI.MeasureTheory.SelfSimilar.TailConvolution

namespace OAI

universe uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem wordWeight_square_sum (S : System α) (f : α → ℝ)
    (hf : ∑ a, S.weight a*f a=0) (n : ℕ) :
    (∑ w : Fin n → α, S.wordWeight w*(∑ j, f (w j))^2)=
      (n : ℝ)*∑ a, S.weight a*(f a)^2 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    have hmean := S.wordWeight_expect_sum f n
    rw [hf,mul_zero] at hmean
    rw [sum_words_cons]
    simp only [wordWeight_cons,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,add_sq]
    simp_rw [mul_add]
    have ha : (∑ a, ∑ w : Fin n → α, S.weight a*S.wordWeight w*(f a)^2)=
        ∑ a, S.weight a*(f a)^2 := by
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [mul_right_comm (S.weight a)]
      rw [← Finset.mul_sum,S.wordWeight_sum,mul_one]
    have hb : (∑ a, ∑ w : Fin n → α,
        S.weight a*S.wordWeight w*(2*f a*∑ j, f (w j)))=0 := by
      apply Finset.sum_eq_zero
      intro a _
      have he (w : Fin n → α) :
          S.weight a*S.wordWeight w*(2*f a*∑ j, f (w j))=
            (2*S.weight a*f a)*(S.wordWeight w*∑ j, f (w j)) := by ring
      simp only [he,← Finset.mul_sum,hmean,mul_zero]
    have hc : (∑ a, ∑ w : Fin n → α,
        S.weight a*S.wordWeight w*(∑ j, f (w j))^2)=
          (n : ℝ)*∑ a, S.weight a*(f a)^2 := by
      simp only [mul_assoc,← Finset.mul_sum,ih,← Finset.sum_mul,S.weight_sum,one_mul]
    simp_rw [Finset.sum_add_distrib]
    rw [ha,hb,hc]
    push_cast
    ring

noncomputable def wordDepth (S : System α) {n : ℕ} (w : Fin n → α) : ℝ :=
  -Real.log |(S.completeMap w).1|/Real.log 2

noncomputable def letterDepth (S : System α) (a : α) : ℝ :=
  -Real.log |S.ratio a|/Real.log 2

theorem wordDepth_sum (S : System α) {n : ℕ} (w : Fin n → α) :
    S.wordDepth w=∑ j, S.letterDepth (w j) := by
  simp only [wordDepth,letterDepth,S.completeMap_log_slope,← Finset.sum_div,← Finset.sum_neg_distrib]

theorem letterDepth_mean (S : System α) :
    ∑ a, S.weight a*S.letterDepth a=S.lyapunov := by
  simp only [letterDepth,lyapunov,neg_div,mul_neg,Finset.sum_neg_distrib]

theorem letterDepth_pos (S : System α) (a : α) : 0 < S.letterDepth a :=
  div_pos (neg_pos.mpr (Real.log_neg (S.ratio_pos a) (S.ratio_lt_one a)))
    (Real.log_pos (by norm_num))

theorem wordDepth_nonneg (S : System α) {n : ℕ} (w : Fin n → α) : 0 ≤ S.wordDepth w := by
  rw [S.wordDepth_sum]
  exact Finset.sum_nonneg (fun j _ => (S.letterDepth_pos (w j)).le)

noncomputable def depthVariance (S : System α) : ℝ :=
  ∑ a, S.weight a*(S.letterDepth a-S.lyapunov)^2

theorem depthVariance_nonneg (S : System α) : 0 ≤ S.depthVariance :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (S.weight_pos a).le (sq_nonneg _))

theorem wordDepth_centered_square (S : System α) (n : ℕ) :
    (∑ w : Fin n → α, S.wordWeight w*(S.wordDepth w-n*S.lyapunov)^2)=
      (n : ℝ)*S.depthVariance := by
  have hf : ∑ a, S.weight a*(S.letterDepth a-S.lyapunov)=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,S.weight_sum,one_mul,S.letterDepth_mean,sub_self]
  have he (w : Fin n → α) : (∑ j, (S.letterDepth (w j)-S.lyapunov))=
      S.wordDepth w-n*S.lyapunov := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,S.wordDepth_sum]
  simpa only [he,depthVariance] using S.wordWeight_square_sum (fun a => S.letterDepth a-S.lyapunov) hf n

theorem depth_bad_mass_bound (S : System α) {A : ℝ} (hA : S.lyapunov < A)
    {n : ℕ} (hn : 0 < n) :
    (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0) ≤
      S.depthVariance/((n : ℝ)*(A-S.lyapunov)^2) := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hd : 0 < A-S.lyapunov := sub_pos.mpr hA
  have hh : (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0)*
      ((n : ℝ)*(A-S.lyapunov))^2 ≤ (n : ℝ)*S.depthVariance := by
    rw [← S.wordDepth_centered_square,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro w _
    split_ifs with h
    · have ht : (n : ℝ)*(A-S.lyapunov) < S.wordDepth w-n*S.lyapunov := by nlinarith
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (mul_pos hnR hd).le ((mul_pos hnR hd).le.trans ht.le)).mpr ht.le)
        (S.wordWeight_pos w).le
    · simp only [zero_mul]
      exact mul_nonneg (S.wordWeight_pos w).le (sq_nonneg _)
  apply (le_div_iff₀ (mul_pos hnR (sq_pos_of_pos hd))).mpr
  have he : (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0)*
      ((n : ℝ)*(A-S.lyapunov))^2 =
      (n : ℝ)*((∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0)*
        ((n : ℝ)*(A-S.lyapunov)^2)) := by ring
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ hnR).mp hh

end EntropyRateDimension.System

end OAI
