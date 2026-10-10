import OAI.NumberTheory.TwoPoint.Bounds.CrudeNumericalWordSum

namespace OAI

/-! The complete numerical trace catalog has the required crude exponential cost. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- This includes signs, all equality patterns, numerical tuple/padding
primes, the step weights, singleton multiplicities, and external dimensions. -/
theorem crude_trace_catalog_exp_bound (R T S : ℕ) (P Q : Finset ℕ)
    (F : Finset (Fin R → SignedStep)) (L C Cexternal Csingle external : ℝ)
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hRscale : (R : ℝ) ≤ 2 * L)
    (hC : 0 ≤ C) (hCe : 0 ≤ Cexternal)
    (hS : (S : ℝ) ≤ Csingle * L * Real.log L)
    (hext : external ≤ Real.exp (Cexternal * L))
    (hslots : (T : ℝ) ≤ C * R * Real.log L)
    (hT : (T : ℝ) + 1 ≤ L ^ (2 : ℕ)) (hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hP : primeHarmonicMass P ≤ L ^ (2 : ℕ)) (hQ : primeHarmonicMass Q ≤ L ^ (2 : ℕ))
    (hactual : ∀ w ∈ F, Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ w ∈ F, ∀ i, Squarefree (w i).tuple)
    (hq : ∀ w ∈ F, ∀ i, Squarefree (w i).padding)
    (htP : ∀ w ∈ F, ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hqQ : ∀ w ∈ F, ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ w ∈ F, ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (hpad : ∀ w ∈ F, ∀ i, ((w i).padding.primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    (∑ w ∈ F, crudeTraceWeight R S (fun i => (w i).padding) L external *
      ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹) ≤
      Real.exp ((Cexternal + Csingle + 408 + 14 * C) * L * (Real.log L) ^ 2) := by
  let W := Real.exp ((Cexternal + Csingle + 402) * L * (Real.log L) ^ 2)
  have hW : 0 ≤ W := (Real.exp_pos _).le
  have hweight (w) (hw : w ∈ F) :
      crudeTraceWeight R S (fun i => (w i).padding) L external ≤ W :=
    crudeTraceWeight_exp_bound R S (fun i => (w i).padding) L external Cexternal Csingle
      hL hlog hRscale hS hCe hext (hpad w hw)
  have hm := numerical_word_reciprocal_sum_le R T P Q F (fun _ => 1) 1 (L ^ (2 : ℕ))
    (by norm_num) (one_le_pow₀ hL) hP hQ (fun _ _ => le_rfl)
    hactual ht hq htP hqQ hd
  simp only [one_mul] at hm
  have hc := crude_numerical_cost_exp_bound R T 2 L C (L ^ (2 : ℕ)) hR
    (lt_of_lt_of_le zero_lt_one hL) hlog hslots hT hRpoly (one_le_pow₀ hL) le_rfl
  have hc' : (∑ w ∈ F, ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹) ≤
      Real.exp ((6 + 14 * C) * L * (Real.log L) ^ 2) := by
    apply (hm.trans hc).trans
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    have hh := mul_le_mul_of_nonneg_right hRscale
      (show 0 ≤ (3 + 7 * C) * (Real.log L) ^ 2 by positivity)
    nlinarith
  calc
    _ ≤ ∑ w ∈ F, W * ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
      apply sum_le_sum
      intro w hw
      exact mul_le_mul_of_nonneg_right (hweight w hw) (by positivity)
    _ = W * ∑ w ∈ F, ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ :=
      (mul_sum _ _ _).symm
    _ ≤ W * Real.exp ((6 + 14 * C) * L * (Real.log L) ^ 2) :=
      mul_le_mul_of_nonneg_left hc' hW
    _ = _ := by dsimp [W]; rw [← Real.exp_add]; congr 1; ring

end TwoPointCorrelations

end OAI
