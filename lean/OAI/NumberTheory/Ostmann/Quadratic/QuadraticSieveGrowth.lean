import Mathlib.Data.Nat.Cast.Order.Field
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveInitial

namespace OAI

/-! # The precise exponent induction for the actual quadratic-sieve matrices -/

namespace Ostmann

/-- Heath-Brown's induction statement, with an arbitrary small-power loss. -/
def QuadraticSieveGrowth (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 1 ≤ M → 1 ≤ N →
    QuadraticSieveBound M N
      (C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ ξ))

theorem quadratic_sieve_growth_two : QuadraticSieveGrowth 2 := by
  intro ε hε
  refine ⟨4, by norm_num, ?_⟩
  intro M N hM hN
  apply (quadraticSieveBound_initial M N hM hN).mono_constant
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hprod := one_le_mul_of_one_le_of_one_le hMR hNR
  have hp : 1 ≤ ((M : ℝ) * N) ^ ε := Real.one_le_rpow hprod hε.le
  have hs : 0 ≤ (M : ℝ) + (N : ℝ) ^ 2 := by positivity
  rw [Real.rpow_two]
  nlinarith

theorem quadratic_growth_shortened_transpose {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B N d : ℕ, 1 ≤ B → 1 ≤ d → d ≤ N →
      QuadraticSieveBound B (N / d)
        (C * ((B : ℝ) * N) ^ ε * ((B : ℝ) ^ ξ + (N : ℝ) / d)) := by
  obtain ⟨C, hC, hc⟩ := h ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro B N d hB hd hdN
  have hdiv : 1 ≤ N / d := Nat.div_pos hdN hd
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hd.trans hdN
  have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hfloorN : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
  have hfactor : 0 ≤ C * (((N / d : ℕ) : ℝ) * B) ^ ε * (((N / d : ℕ) : ℝ) + (B : ℝ) ^ ξ) := by positivity
  apply ((hc (N / d) B hdiv hB).transpose hfactor).mono_constant
  have hp : (((N / d : ℕ) : ℝ) * B) ^ ε ≤ ((B : ℝ) * N) ^ ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    nlinarith [mul_le_mul_of_nonneg_right hfloorN hBR.le]
  calc
    _ = (2 * C) * (((N / d : ℕ) : ℝ) * B) ^ ε * ((B : ℝ) ^ ξ + ((N / d : ℕ) : ℝ)) := by ring
    _ ≤ _ := by gcongr

end Ostmann

end OAI
