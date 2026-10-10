import Mathlib.Analysis.InnerProductSpace.Calculus
import OAI.NumberTheory.Ostmann.ExponentialSum
import OAI.NumberTheory.Ostmann.SharpSieveCircle
import OAI.NumberTheory.Ostmann.SharpSieveCoefficients
import OAI.NumberTheory.Ostmann.SharpSieveEnergy
import OAI.NumberTheory.Ostmann.SharpSieveParseval
import OAI.NumberTheory.Ostmann.SharpSieveSampling
import OAI.NumberTheory.Ostmann.SharpSieveSpacing

namespace OAI

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

theorem sum_trigPoly_sq_le {ι : Type*} [Fintype ι]
    (N : ℕ) (a : ℕ → ℂ) (θ : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ |θ i - θ j|) :
    (∑ i, ‖trigPoly N a (θ i)‖ ^ 2) ≤
      (2 / δ + 8 * Real.pi * N) * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [trigPoly]
  have hc : 0 < 2 * Real.pi * (N : ℝ) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
  have hE : 0 ≤ ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hf := trigPoly_continuous N a
  have hg := trigPolyDeriv_continuous N a
  have hs := separated_sampling_bound θ δ hδ.le hδ₁ hθ hsep
    (fun t => ‖trigPoly N a t‖ ^ 2)
    (fun t => 2 * inner ℝ (trigPoly N a t) (trigPolyDeriv N a t))
    (hf.norm.pow 2) ((hf.inner hg).const_mul 2)
    (fun t => (trigPoly_hasDerivAt N a t).norm_sq) (fun t _ => sq_nonneg _)
  have hv := integral_abs_two_inner_le_energy (trigPoly N a) (trigPolyDeriv N a)
    hf hg (a := 0) (b := 2) (by norm_num) hc
  rw [trigPoly_parseval_two] at hs hv
  have hs' := hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hδ.le))
  have hb := sampling_energy_algebra hδ hc hE (trigPoly_deriv_energy_le_two N a) hs'
  convert hb using 1
  ring

theorem sum_trigPoly_sq_le_32 {ι : Type*} [Fintype ι]
    (N : ℕ) (a : ℕ → ℂ) (θ : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ |θ i - θ j|) :
    (∑ i, ‖trigPoly N a (θ i)‖ ^ 2) ≤
      32 * ((N : ℝ) + δ⁻¹) * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) := by
  apply (sum_trigPoly_sq_le N a θ δ hδ hδ₁ hθ hsep).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hpi := mul_le_mul_of_nonneg_right Real.pi_le_four (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hi := inv_nonneg.mpr hδ.le
  rw [div_eq_mul_inv]
  nlinarith

theorem sum_circleTrigPoly_sq_le {ι : Type*} [Fintype ι]
    (N : ℕ) (a : ℕ → ℂ) (θ : ι → UnitAddCircle) (δ : ℝ)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (θ i) (θ j)) :
    (∑ i, ‖circleTrigPoly N a (θ i)‖ ^ 2) ≤
      32 * ((N : ℝ) + δ⁻¹) * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) := by
  simpa only [trigPoly_circleRepr] using
    sum_trigPoly_sq_le_32 N a (fun i => circleRepr (θ i)) δ hδ hδ₁
      (fun i => circleRepr_mem_Icc (θ i)) (circleRepr_separated θ δ hsep)

theorem sum_trigPoly_sq_reducedFrequency_le (N Q : ℕ) (a : ℕ → ℂ) (hQ : 0 < Q) :
    (∑ f : SharpSieve.ReducedFrequency Q, ‖trigPoly N a f.value‖ ^ 2) ≤
      32 * ((N : ℝ) + (Q : ℝ) ^ 2) * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by positivity
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hδ₁ : (1 : ℝ) / (Q : ℝ) ^ 2 ≤ 1 :=
    (div_le_one (by positivity)).mpr (by nlinarith)
  have h := sum_trigPoly_sq_le_32 N a (fun f : SharpSieve.ReducedFrequency Q => f.value)
    (1 / (Q : ℝ) ^ 2) hδ hδ₁
    (fun f => ⟨f.value_nonneg, f.value_lt_one.le⟩)
    (fun f g hfg => by simpa using SharpSieve.ReducedFrequency.mod_one_spacing hfg 0)
  simpa only [one_div, inv_inv] using h

theorem trigPoly_normalizedCoefficients (s : Finset ℕ) (N : ℕ)
    (hs : s ⊆ Finset.range N) (t : ℝ) :
    trigPoly N (normalizedCoefficients s) t = normalizedExpSum s t := by
  classical
  unfold trigPoly normalizedExpSum
  calc
    (∑ n ∈ Finset.range N, normalizedCoefficients s n *
        Complex.exp (2 * Real.pi * Complex.I * n * t)) =
        ∑ n ∈ s, normalizedCoefficients s n *
          Complex.exp (2 * Real.pi * Complex.I * n * t) := by
      symm
      exact Finset.sum_subset hs (by
        intro n hn hns
        simp [normalizedCoefficients, hns])
    _ = ∑ n ∈ s, (s.card : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * n * t) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [normalizedCoefficients, hn]
    _ = _ := by rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem sum_normalizedExpSum_sq_reducedFrequency_le
    (s : Finset ℕ) (N Q : ℕ) (hs : s ⊆ Finset.range N) (hQ : 0 < Q) :
    (∑ f : SharpSieve.ReducedFrequency Q, ‖normalizedExpSum s f.value‖ ^ 2) ≤
      32 * ((N : ℝ) + (Q : ℝ) ^ 2) / (s.card : ℝ) := by
  have h := sum_trigPoly_sq_reducedFrequency_le N Q (normalizedCoefficients s) hQ
  simp_rw [trigPoly_normalizedCoefficients s N hs] at h
  rw [normalizedCoefficients_energy s N hs] at h
  simpa only [div_eq_mul_inv] using h

theorem sum_normalizedExpSum_sq_le_of_le_sq
    (s : Finset ℕ) (Q : ℕ) (hs : ∀ n ∈ s, n ≤ Q ^ 2) (hQ : 0 < Q) :
    (∑ f : SharpSieve.ReducedFrequency Q, ‖normalizedExpSum s f.value‖ ^ 2) ≤
      96 * (Q : ℝ) ^ 2 / (s.card : ℝ) := by
  have hsub : s ⊆ Finset.range (Q ^ 2 + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hs n hn))
  apply (sum_normalizedExpSum_sq_reducedFrequency_le s (Q ^ 2 + 1) Q hsub hQ).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  push_cast
  nlinarith

end Ostmann

end OAI
