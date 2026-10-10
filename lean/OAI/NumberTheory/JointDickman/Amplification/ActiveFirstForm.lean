import OAI.NumberTheory.JointDickman.Amplification.AmplificationFirstForm
import OAI.NumberTheory.JointDickman.Arithmetic.AmplificationSmoothCutoff

namespace OAI

/-! # Restricting the Cauchy volume to the actual multiplier range -/

namespace JointDickman
open Finset

noncomputable def activeFirstFormWeight (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (T N : ℕ) (D : Finset ℕ) (m : ℕ) : ℝ :=
  if T*(∏ p ∈ D, p)*m < N then firstFormWeight B L τ C u D m else 0

noncomputable def activeFirstFormVolume (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (T N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    activeFirstFormWeight B L τ C u T N i.1 i.2) / (N : ℝ)

theorem firstFormInner_eq_zero_of_inactive (B L : ℕ) (τ C : ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (T N : ℕ)
    (hv : ∀ a c, v a c ≠ 0 → T*c ≤ a) (D : Finset ℕ) (m : ℕ)
    (hm : ¬ T*(∏ p ∈ D, p)*m < N) : firstFormInner B L τ C v J N D m = 0 := by
  classical
  unfold firstFormInner
  apply sum_eq_zero
  intro A _
  dsimp only
  split_ifs with h
  · have hz : v (∏ p ∈ A, p) (∏ p ∈ D, p) = 0 := by
      by_contra hn
      have hle := Nat.mul_le_mul_right m (hv _ _ hn)
      exact hm (hle.trans_lt h.1)
    simp only [hz, mul_zero, Complex.ofReal_zero, zero_mul]
  · rfl

theorem activeFirstFormWeight_nonneg (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (hu : ∀ c, 0 ≤ u c) (T N : ℕ) (D : Finset ℕ) (m : ℕ) :
    0 ≤ activeFirstFormWeight B L τ C u T N D m := by
  unfold activeFirstFormWeight
  split_ifs
  · exact firstFormWeight_nonneg B L τ C u hu D m
  · rfl

/-- The Cauchy volume only counts multipliers permitted by the smooth
coefficient window, giving the factor 1/(Tc) in its later mean estimate. -/
theorem firstDivisorForm_active_cauchy (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (g J : ℕ → ℂ) (T N : ℕ)
    (hu : ∀ c, 0 ≤ u c) (hg : ∀ m, ‖g m‖ ≤ 1)
    (hv : ∀ a c, v a c ≠ 0 → T*c ≤ a) :
    ‖firstDivisorForm B L τ C u v g J N‖^2 ≤
      activeFirstFormVolume B L τ C u T N * firstFormEnergy B L τ C u v J N := by
  classical
  have hp (D : Finset ℕ) (m : ℕ) :
      (activeFirstFormWeight B L τ C u T N D m : ℂ) * star (g m) *
        firstFormInner B L τ C v J N D m =
      (firstFormWeight B L τ C u D m : ℂ) * star (g m) *
        firstFormInner B L τ C v J N D m := by
    unfold activeFirstFormWeight
    split_ifs with hm
    · rfl
    · rw [firstFormInner_eq_zero_of_inactive B L τ C v J T N hv D m hm]
      simp
  have he (D : Finset ℕ) (m : ℕ) :
      activeFirstFormWeight B L τ C u T N D m * ‖firstFormInner B L τ C v J N D m‖^2 =
      firstFormWeight B L τ C u D m * ‖firstFormInner B L τ C v J N D m‖^2 := by
    unfold activeFirstFormWeight
    split_ifs with hm
    · rfl
    · rw [firstFormInner_eq_zero_of_inactive B L τ C v J T N hv D m hm]
      simp
  have h := normalized_weighted_complex_cauchy (ι := Finset ℕ × ℕ)
    ((auxiliaryPrimes B).powerset ×ˢ range N)
    (fun i => activeFirstFormWeight B L τ C u T N i.1 i.2) (fun i => star (g i.2))
    (fun i => firstFormInner B L τ C v J N i.1 i.2)
    (fun i _ => activeFirstFormWeight_nonneg B L τ C u hu T N i.1 i.2)
    (fun i _ => by simpa only [norm_star] using hg i.2) (N := (N : ℝ)) (Nat.cast_nonneg N)
  simpa only [hp, he, firstDivisorForm, activeFirstFormVolume, firstFormEnergy,
    Complex.ofReal_natCast] using h

/-- The concrete bump has the required lower support condition. -/
theorem amplificationBump_ratio_lower (T a c : ℕ)
    (h : amplificationBump (((a : ℝ) / ((T : ℝ)*c))) ≠ 0) : T*c ≤ a := by
  have hs := (amplificationBump_support h).1
  by_cases hc : T*c = 0
  · omega
  have hc0 : (0 : ℝ) < (T : ℝ)*c := by exact_mod_cast (Nat.pos_of_ne_zero hc)
  have ha := (lt_div_iff₀ hc0).mp hs
  norm_num at ha
  exact_mod_cast ha.le

end JointDickman

end OAI
