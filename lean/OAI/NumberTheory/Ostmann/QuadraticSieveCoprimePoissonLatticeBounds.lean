import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import OAI.NumberTheory.Ostmann.QuadraticSievePoissonDilation

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

noncomputable def integerInvSquareMass : ℝ := ∑' n : ℤ, (|(n : ℝ)| ^ 2)⁻¹

theorem summable_integer_inv_sq : Summable (fun n : ℤ => (|(n : ℝ)| ^ 2)⁻¹) := by
  have h := Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)
  simpa only [Real.rpow_neg (abs_nonneg _), Real.rpow_two] using h

theorem integerInvSquareMass_pos : 0 < integerInvSquareMass := by
  have h := summable_integer_inv_sq.le_tsum (1 : ℤ)
    (fun n _ => inv_nonneg.mpr (sq_nonneg _))
  norm_num [integerInvSquareMass] at h ⊢
  linarith

theorem schwartz_restricted_lattice_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y L : ℝ), 0 < y → 0 < L → ∀ S : Set ℤ,
      (∀ n ∈ S, L ≤ |(n : ℝ)|) →
      ‖∑' n : ℤ, S.indicator (fun m : ℤ => ψ ((m : ℝ) * y)) n‖ ≤
        C / (y ^ (A + 2) * L ^ A) := by
  obtain ⟨D, hD, hb⟩ := ψ.decay (A + 2) 0
  simp only [norm_iteratedFDeriv_zero] at hb
  refine ⟨D * integerInvSquareMass, mul_pos hD integerInvSquareMass_pos, ?_⟩
  intro y L hy hL S hS
  have hf : Summable (fun n : ℤ => ψ ((n : ℝ) * y)) := by
    simpa only [dilatedSchwartz_apply, mul_comm] using
      schwartz_summable_int (dilatedSchwartz y hy.ne' ψ)
  have hsf := hf.indicator S
  have hp (n : ℤ) :
      ‖S.indicator (fun m : ℤ => ψ ((m : ℝ) * y)) n‖ ≤
        (D / (y ^ (A + 2) * L ^ A)) * (|(n : ℝ)| ^ 2)⁻¹ := by
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn]
      have hnpos : 0 < |(n : ℝ)| := hL.trans_le (hS n hn)
      have hb' : ‖ψ ((n : ℝ) * y)‖ ≤ D / (|(n : ℝ)| ^ (A + 2) * y ^ (A + 2)) := by
        apply (le_div_iff₀ (by positivity)).mpr
        have hh := hb ((n : ℝ) * y)
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos hy, mul_pow, mul_comm] using hh
      calc
        _ ≤ D / (|(n : ℝ)| ^ (A + 2) * y ^ (A + 2)) := hb'
        _ ≤ D / (L ^ A * |(n : ℝ)| ^ 2 * y ^ (A + 2)) := by
          apply div_le_div_of_nonneg_left hD.le (by positivity)
          calc
            L ^ A * |(n : ℝ)| ^ 2 * y ^ (A + 2) ≤
                (|(n : ℝ)| ^ A * |(n : ℝ)| ^ 2) * y ^ (A + 2) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL.le (hS n hn) A)
                  (sq_nonneg _)) (by positivity)
            _ = _ := by simp only [pow_add]
        _ = _ := by field_simp
    · simp only [Set.indicator_of_notMem hn, norm_zero]
      positivity
  calc
    _ ≤ ∑' n : ℤ, ‖S.indicator (fun m : ℤ => ψ ((m : ℝ) * y)) n‖ :=
      norm_tsum_le_tsum_norm hsf.norm
    _ ≤ ∑' n : ℤ, (D / (y ^ (A + 2) * L ^ A)) * (|(n : ℝ)| ^ 2)⁻¹ :=
      Summable.tsum_le_tsum hp hsf.norm (summable_integer_inv_sq.mul_left _)
    _ = _ := by rw [tsum_mul_left]; unfold integerInvSquareMass; ring

noncomputable def nonzeroLattice (ψ : 𝓢(ℝ, ℂ)) (y : ℝ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else ψ ((n : ℝ) * y)

noncomputable def latticeTail (ψ : 𝓢(ℝ, ℂ)) (y L : ℝ) : ℂ :=
  ∑' n : ℤ, if L < |(n : ℝ)| then ψ ((n : ℝ) * y) else 0

theorem nonzeroLattice_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖nonzeroLattice ψ y‖ ≤ C / y ^ (A + 2) := by
  obtain ⟨C, hC, hb⟩ := schwartz_restricted_lattice_bound ψ A
  refine ⟨C, hC, ?_⟩
  intro y hy
  have h := hb y 1 hy (by norm_num) {n : ℤ | n ≠ 0} (by
    intro n hn
    have hi : (1 : ℕ) ≤ n.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn)
    have hi' : (1 : ℤ) ≤ (n.natAbs : ℤ) := by exact_mod_cast hi
    rw [Int.natCast_natAbs] at hi'
    exact_mod_cast hi')
  simpa only [one_pow, mul_one, nonzeroLattice, Set.indicator_apply, Set.mem_ofPred_eq,
    ite_not] using h

theorem latticeTail_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y L : ℝ), 0 < y → 0 < L →
      ‖latticeTail ψ y L‖ ≤ C / (y ^ (A + 2) * L ^ A) := by
  obtain ⟨C, hC, hb⟩ := schwartz_restricted_lattice_bound ψ A
  refine ⟨C, hC, ?_⟩
  intro y L hy hL
  have h := hb y L hy hL {n : ℤ | L < |(n : ℝ)|} (fun n hn => hn.le)
  simpa only [latticeTail, Set.indicator_apply, Set.mem_ofPred_eq] using h

end Ostmann.QuadraticSieve

end OAI
