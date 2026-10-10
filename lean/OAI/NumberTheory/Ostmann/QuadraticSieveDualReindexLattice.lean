import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonLatticeBounds
import OAI.NumberTheory.Ostmann.QuadraticSieveDualReindex

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform

theorem schwartz_injective_weighted_lattice_bound {ι : Type*} (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : ι → ℤ), Function.Injective ν →
      ∀ (w : ι → ℂ), (∀ i, ‖w i‖ ≤ 1) → ∀ (y L : ℝ), 0 < y → 0 < L →
      (∀ i, w i ≠ 0 → L ≤ |(ν i : ℝ)|) →
      ‖∑' i, w i * ψ ((ν i : ℝ) * y)‖ ≤ C / (y ^ (A + 2) * L ^ A) := by
  obtain ⟨D, hD, hb⟩ := ψ.decay (A + 2) 0
  simp only [norm_iteratedFDeriv_zero] at hb
  refine ⟨D * integerInvSquareMass, mul_pos hD integerInvSquareMass_pos, ?_⟩
  intro ν hν w hw y L hy hL hcut
  have hint : Summable (fun n : ℤ => ψ ((n : ℝ) * y)) := by
    simpa only [dilatedSchwartz_apply, mul_comm] using
      schwartz_summable_int (dilatedSchwartz y hy.ne' ψ)
  have hbase : Summable (fun i => ψ ((ν i : ℝ) * y)) := hint.comp_injective hν
  have hsum : Summable (fun i => w i * ψ ((ν i : ℝ) * y)) := by
    apply hbase.norm.of_norm_bounded
    intro i
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _)
  have hinv : Summable (fun i => (|(ν i : ℝ)| ^ 2)⁻¹) :=
    summable_integer_inv_sq.comp_injective hν
  have hmass : (∑' i, (|(ν i : ℝ)| ^ 2)⁻¹) ≤ integerInvSquareMass := by
    exact Summable.tsum_le_tsum_of_inj ν hν (fun n hn => inv_nonneg.mpr (sq_nonneg _))
      (fun i => le_rfl) hinv summable_integer_inv_sq
  have hp (i : ι) : ‖w i * ψ ((ν i : ℝ) * y)‖ ≤
      (D / (y ^ (A + 2) * L ^ A)) * (|(ν i : ℝ)| ^ 2)⁻¹ := by
    by_cases hi : w i = 0
    · rw [hi, zero_mul, norm_zero]
      positivity
    · have hni : 0 < |(ν i : ℝ)| := hL.trans_le (hcut i hi)
      have hb' : ‖ψ ((ν i : ℝ) * y)‖ ≤
          D / (|(ν i : ℝ)| ^ (A + 2) * y ^ (A + 2)) := by
        apply (le_div_iff₀ (by positivity)).mpr
        have hh := hb ((ν i : ℝ) * y)
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos hy, mul_pow, mul_comm] using hh
      calc
        _ ≤ ‖ψ ((ν i : ℝ) * y)‖ := by
          rw [norm_mul]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _)
        _ ≤ D / (|(ν i : ℝ)| ^ (A + 2) * y ^ (A + 2)) := hb'
        _ ≤ D / (L ^ A * |(ν i : ℝ)| ^ 2 * y ^ (A + 2)) := by
          apply div_le_div_of_nonneg_left hD.le (by positivity)
          calc
            _ ≤ (|(ν i : ℝ)| ^ A * |(ν i : ℝ)| ^ 2) * y ^ (A + 2) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL.le (hcut i hi) A)
                  (sq_nonneg _)) (by positivity)
            _ = _ := by simp only [pow_add]
        _ = _ := by field_simp
  calc
    _ ≤ ∑' i, ‖w i * ψ ((ν i : ℝ) * y)‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' i, (D / (y ^ (A + 2) * L ^ A)) * (|(ν i : ℝ)| ^ 2)⁻¹ :=
      Summable.tsum_le_tsum hp hsum.norm (hinv.mul_left _)
    _ = (D / (y ^ (A + 2) * L ^ A)) * (∑' i, (|(ν i : ℝ)| ^ 2)⁻¹) := tsum_mul_left
    _ ≤ (D / (y ^ (A + 2) * L ^ A)) * integerInvSquareMass :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
