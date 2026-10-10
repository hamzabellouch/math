import OAI.Analysis.MarkovType.CoefficientSequenceOps
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coefficientMonotone_upper_pow {m : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (hblock : ∀ (y : Fin m → E) (R : ℝ), 0 ≤ R →
      CoefficientMonotone y → (∀ i, ‖y i‖ ≤ R) →
      ‖∑ i, y i‖ ≤ β * R)
    (k : ℕ) {n : ℕ} (hn : n ≤ m ^ k) (x : Fin n → E)
    (hx : CoefficientMonotone x) {R : ℝ} (hR : 0 ≤ R)
    (hnorm : ∀ i, ‖x i‖ ≤ R) : ‖∑ i, x i‖ ≤ β ^ k * R := by
  induction k generalizing n R with
  | zero =>
      cases n with
      | zero => simpa using hR
      | succ n =>
          have hn0 : n = 0 := by
            apply Nat.eq_zero_of_le_zero
            apply Nat.le_of_succ_le_succ
            simpa only [pow_zero, Nat.succ_eq_add_one, Nat.zero_add] using hn
          subst n
          simpa [Fin.sum_univ_one] using hnorm (0 : Fin 1)
  | succ k ih =>
      have hpad : n ≤ m * m ^ k := by simpa only [pow_succ'] using hn
      let y : Fin (m * m ^ k) → E := coefficientZeroPad x hpad
      have hy : CoefficientMonotone y := hx.zeroPad hpad
      have hyNorm : ∀ i, ‖y i‖ ≤ R := norm_coefficientZeroPad_le x hpad hR hnorm
      have hrows : ∀ j, ‖equalBlocks y j‖ ≤ β ^ k * R := by
        intro j
        exact ih le_rfl (equalBlock y j) (hy.equalBlock j) hR
          (fun i => hyNorm (finProdFinEquiv (j, i)))
      have hbound := hblock (equalBlocks y) (β ^ k * R)
        (mul_nonneg (pow_nonneg hβ k) hR) hy.equalBlocks hrows
      calc
        ‖∑ i, x i‖ = ‖∑ j, equalBlocks y j‖ := by
          rw [sum_equalBlocks]
          exact congrArg norm (sum_coefficientZeroPad x hpad).symm
        _ ≤ β * (β ^ k * R) := hbound
        _ = β ^ (k + 1) * R := by rw [pow_succ', mul_assoc]

theorem coefficientMonotone_upper_length {m : ℕ} {β α : ℝ}
    (hm : 1 < m) (hα : 0 < α) (hscale : (m : ℝ) ^ α = β)
    (hblock : ∀ (y : Fin m → E) (R : ℝ), 0 ≤ R →
      CoefficientMonotone y → (∀ i, ‖y i‖ ≤ R) →
      ‖∑ i, y i‖ ≤ β * R)
    {n : ℕ} (x : Fin n → E) (hx : CoefficientMonotone x)
    {R : ℝ} (hR : 0 ≤ R) (hnorm : ∀ i, ‖x i‖ ≤ R) :
    ‖∑ i, x i‖ ≤ β * (n : ℝ) ^ α * R := by
  by_cases hn0 : n = 0
  · subst n
    simp [Real.zero_rpow hα.ne']
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hm1 : (1 : ℝ) ≤ m := by
    simpa only [Nat.cast_one] using (Nat.cast_le.mpr hm.le : ((1 : ℕ) : ℝ) ≤ (m : ℝ))
  have hβ1 : 1 ≤ β := by
    rw [← hscale]
    exact Real.one_le_rpow hm1 hα.le
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ1
  have hex : ∃ k : ℕ, n ≤ m ^ k := ⟨n, (n.lt_pow_self hm).le⟩
  let k := Nat.find hex
  have hnk : n ≤ m ^ k := Nat.find_spec hex
  have hfactor : β ^ k ≤ β * (n : ℝ) ^ α := by
    by_cases hk0 : k = 0
    · have hn1 : n = 1 := by
        apply le_antisymm
        · simpa only [hk0, pow_zero] using hnk
        · exact hnpos
      simpa only [hk0, pow_zero, hn1, Nat.cast_one, Real.one_rpow, mul_one] using hβ1
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hprev : m ^ (k - 1) < n := by
        apply lt_of_not_ge
        exact Nat.find_min hex (show k - 1 < Nat.find hex from Nat.sub_lt hkpos (by decide))
      have hprevReal : (m : ℝ) ^ (k - 1) ≤ (n : ℝ) := by
        simpa only [Nat.cast_pow] using
          (Nat.cast_le.mpr hprev.le : ((m ^ (k - 1) : ℕ) : ℝ) ≤ (n : ℝ))
      have hpower : β ^ (k - 1) ≤ (n : ℝ) ^ α := by
        calc
          β ^ (k - 1) = ((m : ℝ) ^ (k - 1)) ^ α := by
            rw [← hscale, Real.rpow_pow_comm (Nat.cast_nonneg m)]
          _ ≤ (n : ℝ) ^ α := Real.rpow_le_rpow
            (pow_nonneg (Nat.cast_nonneg m) _) hprevReal hα.le
      calc
        β ^ k = β * β ^ (k - 1) := by
          rw [← pow_succ']
          congr 1
          exact (Nat.sub_add_cancel hkpos).symm
        _ ≤ β * (n : ℝ) ^ α := mul_le_mul_of_nonneg_left hpower hβ0
  exact (coefficientMonotone_upper_pow hβ0 hblock k hnk x hx hR hnorm).trans
    (mul_le_mul_of_nonneg_right hfactor hR)

theorem exists_upperBlock_exponent {m : ℕ} {β : ℝ}
    (hβ : 1 < β) (hβm : β < (m : ℝ)) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ (m : ℝ) ^ α = β := by
  have hm1 : (1 : ℝ) < m := hβ.trans hβm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans hm1
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  refine ⟨Real.log β / Real.log (m : ℝ),
    div_pos (Real.log_pos hβ) hlogm, ?_, ?_⟩
  · exact (div_lt_one hlogm).2 (Real.log_lt_log hβ0 hβm)
  · rw [Real.rpow_def_of_pos hm0, div_eq_mul_inv, mul_left_comm,
      mul_inv_cancel₀ hlogm.ne', mul_one, Real.exp_log hβ0]

theorem exists_upperBlock_gain_exponent {m : ℕ} {β : ℝ}
    (hm : 1 < m) (hβm : β < (m : ℝ)) :
    ∃ A α : ℝ, β ≤ A ∧ 1 < A ∧ 0 < α ∧ α < 1 ∧ (m : ℝ) ^ α = A := by
  have hm1 : (1 : ℝ) < m := by
    simpa only [Nat.cast_one] using (Nat.cast_lt.mpr hm : ((1 : ℕ) : ℝ) < (m : ℝ))
  have hmax : max β 1 < (m : ℝ) := max_lt_iff.mpr ⟨hβm, hm1⟩
  let A : ℝ := ((m : ℝ) + max β 1) / 2
  have hβA : β ≤ A := by
    have hbmax := le_max_left β 1
    dsimp [A]
    linarith
  have hA1 : 1 < A := by
    have h1max := le_max_right β 1
    dsimp [A]
    linarith
  have hAm : A < (m : ℝ) := by
    dsimp [A]
    linarith
  obtain ⟨α, hα0, hα1, hscale⟩ := exists_upperBlock_exponent hA1 hAm
  exact ⟨A, α, hβA, hA1, hα0, hα1, hscale⟩

theorem coefficientMonotone_upper_exists_power {m : ℕ} {β : ℝ}
    (hm : 1 < m) (hβm : β < (m : ℝ))
    (hblock : ∀ (y : Fin m → E) (R : ℝ), 0 ≤ R →
      CoefficientMonotone y → (∀ i, ‖y i‖ ≤ R) →
      ‖∑ i, y i‖ ≤ β * R) :
    ∃ A α : ℝ, 1 < A ∧ 0 < α ∧ α < 1 ∧
      ∀ (n : ℕ) (x : Fin n → E) (R : ℝ), 0 ≤ R →
        CoefficientMonotone x → (∀ i, ‖x i‖ ≤ R) →
        ‖∑ i, x i‖ ≤ A * (n : ℝ) ^ α * R := by
  obtain ⟨A, α, hβA, hA1, hα0, hα1, hscale⟩ :=
    exists_upperBlock_gain_exponent hm hβm
  have hblockA : ∀ (y : Fin m → E) (R : ℝ), 0 ≤ R →
      CoefficientMonotone y → (∀ i, ‖y i‖ ≤ R) →
      ‖∑ i, y i‖ ≤ A * R := by
    intro y R hR hy hnorm
    exact (hblock y R hR hy hnorm).trans (mul_le_mul_of_nonneg_right hβA hR)
  refine ⟨A, α, hA1, hα0, hα1, ?_⟩
  intro n x R hR hx hnorm
  exact coefficientMonotone_upper_length hm hα0 hscale hblockA x hx hR hnorm

end MarkovSuperreflexivity

end OAI
