import OAI.NumberTheory.CubicMoment.Estimates.DispersionAbsoluteModel

namespace OAI

/-! Direct sparse-branch model counting. Mutual coprimality is not
removed: the original squarefree product factor remains in the sum. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma squarefree_model_bilinear_counting
    (P Q : Finset Eisenstein) (α β : Eisenstein → ℂ) (V : Eisenstein → Eisenstein → ℂ)
    {A B L₁ L₂ H : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (_hH : 0 ≤ H)
    (hP : ∀ a ∈ P, primary a ∧ L₁ ≤ norm a ∧ norm a ≤ A)
    (hQ : ∀ b ∈ Q, primary b ∧ L₂ ≤ norm b ∧ norm b ≤ B)
    (hV : ∀ a ∈ P, ∀ b ∈ Q, ‖V a b‖ ≤ H) :
    ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
      ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖^2 ≤
      (324*H^2)*(A*B)*L₁^(-1/3:ℝ)*L₂^(-1/3:ℝ)*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by
  have hcardP : (P.card:ℝ) ≤ 18*A := by
    apply (Nat.cast_le.mpr (Finset.card_le_card (show P ⊆ primaryElementBall A from ?_))).trans
      (primaryElementBall_card_le hA)
    intro a ha
    exact mem_primaryElementBall.mpr ⟨(hP a ha).1,(hP a ha).2.2⟩
  have hcardQ : (Q.card:ℝ) ≤ 18*B := by
    apply (Nat.cast_le.mpr (Finset.card_le_card (show Q ⊆ primaryElementBall B from ?_))).trans
      (primaryElementBall_card_le hB)
    intro b hb
    exact mem_primaryElementBall.mpr ⟨(hQ b hb).1,(hQ b hb).2.2⟩
  have hnorm :
      ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
        ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖ ≤
      H*dispersionAbsoluteModel P α*dispersionAbsoluteModel Q β := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ a ∈ P, H*(‖α a‖*norm a^(-1/6:ℝ))*
          dispersionAbsoluteModel Q β := by
        apply Finset.sum_le_sum
        intro a ha
        apply (norm_sum_le _ _).trans
        rw [dispersionAbsoluteModel,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro b hb
        have hna := norm_nonneg a
        have hnb := norm_nonneg b
        have hμ : ‖(idealMoebius (a*b):ℂ)^2‖ ≤ 1 := by
          simpa only [norm_pow,one_pow] using
            pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_idealMoebius_le_one (a*b)) 2
        rw [norm_mul,norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),norm_mul_eq,
          Real.mul_rpow (norm_nonneg a) (norm_nonneg b)]
        calc
          _ ≤ ‖α a‖*‖β b‖*1*(norm a^(-1/6:ℝ)*norm b^(-1/6:ℝ))*H := by
            gcongr
            exact hV a ha b hb
          _ = _ := by ring
      _ = _ := by rw [←Finset.sum_mul,←Finset.mul_sum]; rfl
  have heP := dispersionAbsoluteModel_sq_le P α hL₁ (fun a ha => (hP a ha).2.1)
  have heQ := dispersionAbsoluteModel_sq_le Q β hL₂ (fun b hb => (hQ b hb).2.1)
  have hp : 0 ≤ dispersionAbsoluteModel P α := dispersionAbsoluteModel_nonneg _ _
  have hq : 0 ≤ dispersionAbsoluteModel Q β := dispersionAbsoluteModel_nonneg _ _
  calc
    _ ≤ (H*dispersionAbsoluteModel P α*dispersionAbsoluteModel Q β)^2 :=
      pow_le_pow_left₀ (_root_.norm_nonneg _) hnorm 2
    _ = H^2*(dispersionAbsoluteModel P α)^2*(dispersionAbsoluteModel Q β)^2 := by ring
    _ ≤ H^2*((P.card:ℝ)*L₁^(-1/3:ℝ)*(∑ a ∈ P, ‖α a‖^2))*
        ((Q.card:ℝ)*L₂^(-1/3:ℝ)*(∑ b ∈ Q, ‖β b‖^2)) := by
      gcongr
      · simpa only [neg_div] using heP
      · simpa only [neg_div] using heQ
    _ ≤ H^2*((18*A)*L₁^(-1/3:ℝ)*(∑ a ∈ P, ‖α a‖^2))*
        ((18*B)*L₂^(-1/3:ℝ)*(∑ b ∈ Q, ‖β b‖^2)) := by gcongr
    _ = _ := by ring

lemma sparse_model_counting_scale {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 0 < M) :
    (A*B)*(A/M)^(-1/3:ℝ)*(B/M)^(-1/3:ℝ) = M^(2/3:ℝ)*(A*B)^(2/3:ℝ) := by
  rw [Real.div_rpow hA.le hM.le,Real.div_rpow hB.le hM.le,
    Real.mul_rpow hA.le hB.le]
  have ha : A*A^(-1/3:ℝ) = A^(2/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one A]
    rw [←Real.rpow_add hA]
    norm_num
  have hb : B*B^(-1/3:ℝ) = B^(2/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one B]
    rw [←Real.rpow_add hB]
    norm_num
  have hm : M^(-1/3:ℝ)*M^(-1/3:ℝ) = M^(-2/3:ℝ) := by
    rw [←Real.rpow_add hM]
    norm_num
  calc
    (A*B)*(A^(-1/3:ℝ)/M^(-1/3:ℝ))*(B^(-1/3:ℝ)/M^(-1/3:ℝ)) =
        (A*A^(-1/3:ℝ))*(B*B^(-1/3:ℝ))/(M^(-1/3:ℝ)*M^(-1/3:ℝ)) := by ring
    _ = (A^(2/3:ℝ)*B^(2/3:ℝ))/M^(-2/3:ℝ) := by rw [ha,hb,hm]
    _ = M^(2/3:ℝ)*(A^(2/3:ℝ)*B^(2/3:ℝ)) := by
      rw [show (-2/3:ℝ) = -(2/3) by ring,Real.rpow_neg hM.le,div_inv_eq_mul,mul_comm]

/-- The squarefree model has at most the cubic-sieve shape by direct
finite counting. No cancellation or model asymptotic is assumed. -/
lemma squarefree_model_bilinear_operator
    (P Q : Finset Eisenstein) (α β : Eisenstein → ℂ) (V : Eisenstein → Eisenstein → ℂ)
    {A B M H ε : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hM : 0 < M)
    (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hP : ∀ a ∈ P, primary a ∧ A/M ≤ norm a ∧ norm a ≤ A)
    (hQ : ∀ b ∈ Q, primary b ∧ B/M ≤ norm b ∧ norm b ≤ B)
    (hV : ∀ a ∈ P, ∀ b ∈ Q, ‖V a b‖ ≤ H) :
    ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
      ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖^2 ≤
      (324*H^2*M^(2/3:ℝ))*(A*B)^ε*(A+B+(A*B)^(2/3:ℝ))*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hpref : 1 ≤ (A*B)^ε := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hA hB) hε
  have hshape : (A*B)^(2/3:ℝ) ≤ (A*B)^ε*(A+B+(A*B)^(2/3:ℝ)) := by
    calc
      _ ≤ A+B+(A*B)^(2/3:ℝ) := by linarith
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hpref
  apply (squarefree_model_bilinear_counting P Q α β V hAp.le hBp.le
    (div_pos hAp hM) (div_pos hBp hM) hH hP hQ hV).trans
  calc
    _ = (324*H^2*M^(2/3:ℝ))*(A*B)^(2/3:ℝ)*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by
      have hh := sparse_model_counting_scale hAp hBp hM
      calc
        _ = (324*H^2)*((A*B)*(A/M)^(-1/3:ℝ)*(B/M)^(-1/3:ℝ))*
            (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by ring
        _ = _ := by rw [hh]; ring
    _ ≤ (324*H^2*M^(2/3:ℝ))*((A*B)^ε*(A+B+(A*B)^(2/3:ℝ)))*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hshape (by positivity))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
