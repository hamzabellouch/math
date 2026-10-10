import OAI.NumberTheory.DirichletL.Hecke.DetectorProfiles

namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

theorem scaled_derivatives_of_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1+u)^K*‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  let m := Real.exp (-L)
  let H := Real.exp L
  let S : ℝ := ∑ j ∈ Finset.range (K+1), (j.factorial : ℝ)*CF*(H^2)^j
  have hm : 0 < m := Real.exp_pos _
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr hL
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S/m^K,by positivity,?_⟩
  intro R hR j hj y hy
  have hh := FourierBridge.coupled_factor_uniform_derivative F R 1 y m H CF 0 K j hF
    hR hm (Real.exp_le_one_iff.mpr (by linarith)) hH (by simpa using hH)
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).1))
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).2))
    hj hCF (by simpa using hdecay)
  simp only [zero_add, pow_zero, mul_one, one_mul] at hh
  have hs : (j.factorial : ℝ)*CF*(H^2)^j ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (s := Finset.range (K+1))
      (f := fun i => (i.factorial : ℝ)*CF*(H^2)^i) (a := j)
    · intro i hi; positivity
    · exact Finset.mem_range.mpr (by omega)
  exact (le_div_iff₀ (pow_pos hm K)).mpr (by simpa [mul_comm] using hh.trans hs)

theorem scaled_schwartz_derivatives (F : SchwartzMap ℝ ℂ)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay F (F.smooth ⊤) L hL K
    (FourierBridge.schwartzDerivativeDecayConstant F K K)
    (FourierBridge.schwartzDerivativeDecayConstant_nonneg F K K)
  intro i hi u hu
  simpa using FourierBridge.schwartz_derivative_decay_finite F 0 K K i u le_rfl hi hu

theorem scaled_expNeg_derivatives (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => expNeg (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay expNeg expNeg_smooth L hL K
    ((K.factorial : ℝ)*Real.exp 1) (by positivity)
  intro i hi u hu
  exact expNeg_derivative_decay K i u hu

lemma const_one_derivative_norm (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  split_ifs <;> simp

lemma complement_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (C : ℝ) (j : ℕ) (y : ℝ) (hbound : ‖iteratedFDeriv ℝ j F y‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => 1-F z) y‖ ≤ 1+C := by
  change ‖iteratedFDeriv ℝ j ((fun _ : ℝ => (1 : ℂ)) - F) y‖ ≤ _
  rw [iteratedFDeriv_sub contDiff_const (hF.of_le (by simp))]
  change ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y - iteratedFDeriv ℝ j F y‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add (const_one_derivative_norm j y) hbound)

lemma product_derivative_bound (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (K j : ℕ) (hj : j ≤ K) (y : ℝ)
    (hFb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i F y‖ ≤ CF)
    (hGb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i G y‖ ≤ CG) :
    ‖iteratedFDeriv ℝ j (fun z => F z*G z) y‖ ≤ (2 : ℝ)^K*CF*CG := by
  apply (norm_iteratedFDeriv_mul_le hF hG y (n := j) (by simp)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*CF*CG := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb i (hi'.trans hj)) (by positivity))
        (hGb (j-i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*CF*CG := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCF) hCG

end
end SevenEighths.HeckeDetectorProfiles

end OAI
