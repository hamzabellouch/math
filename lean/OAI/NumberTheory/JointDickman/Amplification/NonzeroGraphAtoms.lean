import OAI.NumberTheory.JointDickman.Arithmetic.DivisorGraphSupport

namespace OAI

/-! # Nonzero summands give genuine coprime small-lag graph edges -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem firstFormAtom_nonzero_support (B L T : ℕ) (τ C : ℝ) (J : ℕ → ℂ)
    (N : ℕ) (D A : Finset ℕ) (m : ℕ)
    (h : firstFormAtom B L τ C (amplificationInnerWeight T) J N D m A ≠ 0) :
    (∏ p ∈ A, p)*m < N ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1 ∧
      T*(∏ p ∈ D, p) < (∏ p ∈ A, p) ∧
      (∏ p ∈ A, p) < 2*(T*(∏ p ∈ D, p)) := by
  classical
  unfold firstFormAtom at h
  dsimp only at h
  split_ifs at h with hc
  · have hw : amplificationInnerWeight T (∏ p ∈ A, p) (∏ p ∈ D, p) ≠ 0 := by
      intro he
      simp only [he, mul_zero, Complex.ofReal_zero, zero_mul, ne_eq, not_true_eq_false] at h
    exact ⟨hc.1,hc.2,amplificationInnerWeight_support hw⟩
  · exact False.elim (h rfl)

/-- The actual nonzero atoms satisfy every arithmetic condition used in the
change of variables. Distinct subsets give distinct coefficient integers. -/
theorem nonzero_atoms_small_coprime_lag {B L T : ℕ} (τ C : ℝ) (J : ℕ → ℂ)
    (N : ℕ) {D A E : Finset ℕ} (_hD : D ⊆ auxiliaryPrimes B)
    (hA : A ⊆ auxiliaryPrimes B) (hE : E ⊆ auxiliaryPrimes B) (hAE : A ≠ E)
    (hT : T ≤ auxiliaryCutoff B) (m : ℕ)
    (ha : firstFormAtom B L τ C (amplificationInnerWeight T) J N D m A ≠ 0)
    (hb : firstFormAtom B L τ C (amplificationInnerWeight T) J N D m E ≠ 0) :
    ∃ j : ℤ, j ≠ 0 ∧ j.natAbs < T ∧
      ((∏ p ∈ A, p : ℕ) : ℤ) - (∏ p ∈ E, p : ℕ) = j*(∏ p ∈ D, p : ℕ) ∧
      (∏ p ∈ A, p).Coprime (∏ p ∈ E, p) ∧
      (∏ p ∈ A, p).Coprime (∏ p ∈ D, p) ∧
      (∏ p ∈ E, p).Coprime (∏ p ∈ D, p) ∧
      (∏ p ∈ A, p).Coprime j.natAbs ∧ (∏ p ∈ E, p).Coprime j.natAbs := by
  obtain ⟨haN,hac,hwa⟩ := firstFormAtom_nonzero_support B L T τ C J N D A m ha
  obtain ⟨hbN,hbc,hwb⟩ := firstFormAtom_nonzero_support B L T τ C J N D E m hb
  have hab : (∏ p ∈ A, p) ≠ ∏ p ∈ E, p :=
    fun he => hAE (primeProduct_injective (auxiliaryPrimes_prime B) hA hE he)
  obtain ⟨j,hj0,hj,hjs⟩ := divisor_pair_small_lag hac hbc hab hwa hwb
  have haj := auxiliaryProduct_coprime_small hA (Int.natAbs_pos.mpr hj0) (hjs.le.trans hT)
  have hbj := auxiliaryProduct_coprime_small hE (Int.natAbs_pos.mpr hj0) (hjs.le.trans hT)
  have hac' := (coprime_of_divisor_linear_succ hac).1
  have hbc' := (coprime_of_divisor_linear_succ hbc).1
  exact ⟨j,hj0,hjs,hj,divisor_edge_coprime hac' haj hj,hac',hbc',haj,hbj⟩

/-- The prescribed multiplier is eventually below the lower prime cutoff. -/
theorem amplificationMultiplier_le_cutoff : ∀ᶠ B : ℕ in atTop,
    amplificationMultiplier B ≤ auxiliaryCutoff B := by
  filter_upwards [amplificationMultiplier_comparable,eventually_ge_atTop 1] with B hT hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : (B : ℝ)^(8/25 : ℝ) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hBr (by norm_num : (8/25 : ℝ) ≤ 1)
  have hTB : amplificationMultiplier B ≤ B := by exact_mod_cast hT.2.2.trans hpow
  have hbpow : B ≤ B ^ (1000 : ℕ) := le_self_pow₀ hB (by decide : (1000 : ℕ) ≠ 0)
  exact hTB.trans hbpow

end JointDickman

end OAI
