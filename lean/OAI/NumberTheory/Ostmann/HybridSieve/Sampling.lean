import OAI.NumberTheory.Ostmann.HybridSieve.OrdinateIntegral
import OAI.NumberTheory.Ostmann.HybridSieve.SamplingDerivative
import OAI.NumberTheory.Ostmann.HybridSieve.SamplingFamily

namespace OAI

open scoped BigOperators
open Set MeasureTheory
namespace Ostmann.HybridSieve

theorem physicalDyadicSum_hasDerivAt (N : ℕ) (a : ℕ → ℂ) {Q : ℕ}
    (i : PrimitiveFamily Q) (t : ℝ) :
    HasDerivAt (physicalDyadicSum N a i)
      (physicalDyadicSum N (ordinateDerivativeCoefficients a) i t) t := by
  have h := finite_ordinate_sum_hasDerivAt (Finset.Ioc N (2 * N))
    (fun n => a n * familyValue i n) t
  convert h using 1
  · rfl
  · unfold physicalDyadicSum
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [ordinateDerivativeCoefficients]
    ring

theorem exists_physical_hybrid_sampling_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι], ∀ (N Q : ℕ) (a : ℕ → ℂ) (H : ℝ)
      (character : ι → PrimitiveFamily Q) (γ : ι → ℝ),
      0 < N → 0 < Q → 1 ≤ H → (∀ j, |γ j| ≤ H) →
      (∀ j k, j ≠ k → character j = character k → 1 ≤ |γ j - γ k|) →
      (∑ j, familyWeight (character j) * ‖physicalDyadicSum N a (character j) (γ j)‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + (harmonic (Q ^ 2) : ℝ)) *
          (2 + Real.log (2 * N : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_physical_hybrid_integral_constant
  refine ⟨2 * C, by positivity, ?_⟩
  intro ι _ N Q a H character γ hN hQ hH hγ hsep
  have hHp : 0 < H := by linarith
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hharm : 0 ≤ (harmonic (Q ^ 2) : ℝ) := by
    exact_mod_cast (harmonic_pos (pow_ne_zero 2 (Nat.ne_of_gt hQ))).le
  let E : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
  let B : ℝ := (N : ℝ) + 2 * H + (Q : ℝ) ^ 2 * (2 * H) * (harmonic (Q ^ 2) : ℝ)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi (b : ℕ → ℂ) :
      (∑ i : PrimitiveFamily Q, familyWeight i *
        (∫ t in Icc (-2 * H) (2 * H), ‖physicalDyadicSum N b i t‖ ^ 2)) ≤
        C * B * ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 := by
    have h := hbound N Q b (2 * H) hN (by positivity)
    simp only [intervalIntegral.integral_of_le (show -(2 * H) ≤ 2 * H by linarith),
      ← integral_Icc_eq_integral_Ioc] at h
    simpa only [B, neg_mul] using h
  have hs := family_separated_samples_le_integral character γ familyWeight familyWeight_nonneg
    H hH hγ hsep (fun i => physicalDyadicSum N a i)
    (fun i => physicalDyadicSum N (ordinateDerivativeCoefficients a) i)
    (physicalDyadicSum_continuous N a) (physicalDyadicSum_continuous N _)
    (physicalDyadicSum_hasDerivAt N a)
  have hd := ordinateDerivativeCoefficients_energy N a hN
  have hscale : B ≤ 2 * (((N : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + (harmonic (Q ^ 2) : ℝ))) := by
    have hQ2 : 1 ≤ (Q : ℝ) ^ 2 := by nlinarith
    have hqH : H ≤ (Q : ℝ) ^ 2 * H := by nlinarith
    have hNh : 0 ≤ (N : ℝ) * (harmonic (Q ^ 2) : ℝ) := mul_nonneg (Nat.cast_nonneg _) hharm
    dsimp [B]
    nlinarith
  calc
    _ ≤ 2 * (C * B * E) + C * B *
        (∑ n ∈ Finset.Ioc N (2 * N), ‖ordinateDerivativeCoefficients a n‖ ^ 2) :=
      hs.trans (add_le_add (mul_le_mul_of_nonneg_left (hi a) (by norm_num)) (hi _))
    _ ≤ 2 * (C * B * E) + C * B * (Real.log (2 * N : ℝ) ^ 2 * E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hd (mul_nonneg hC.le hB))
    _ = C * B * (2 + Real.log (2 * N : ℝ) ^ 2) * E := by ring
    _ ≤ C * (2 * (((N : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + (harmonic (Q ^ 2) : ℝ)))) *
        (2 + Real.log (2 * N : ℝ) ^ 2) * E :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hC.le) (by positivity)) hE
    _ = _ := by dsimp [E]; ring

end Ostmann.HybridSieve

end OAI
