import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyLCM
import OAI.NumberTheory.Ostmann.Characters.FrequencyHarmonic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.PairedFrequencyTreeSum
open FrequencyMultiplicity

theorem reduced_sum_le (v w : ℤ) (hv : v ≠ 0) (S : Finset ℤ) (V : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ s ∈ S, f (reducedModulus v w s) ≤
      (2 * ((v.natAbs.gcd w.natAbs).divisors.card : ℝ)) * ∑ a ∈ Finset.Icc 1 V, f a := by
  have hmap : ∀ s ∈ S, reducedModulus v w s ∈ Finset.Icc 1 V :=
    fun s hs => Characters.reducedModulus_mem_Icc v w s (hS s hs).1 V (hS s hs).2
  calc
    _ = ∑ a ∈ Finset.Icc 1 V, ∑ s ∈ S with reducedModulus v w s = a, f a :=
      (Finset.sum_fiberwise_of_maps_to' hmap f).symm
    _ ≤ ∑ a ∈ Finset.Icc 1 V, (2 * ((v.natAbs.gcd w.natAbs).divisors.card : ℝ)) * f a := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (hf a)
      exact_mod_cast reduced_fiber_card v w hv S a
    _ = _ := (Finset.mul_sum _ _ _).symm

def modulus (s v w : ℤ × ℤ) : ℕ :=
  (reducedModulus v.1 w.1 s.1).lcm (reducedModulus v.2 w.2 s.2)

theorem paired_reduced_sum_le (S : Finset (ℤ × ℤ)) (V : ℕ)
    (hS : ∀ s ∈ S, (s.1 ≠ 0 ∧ s.1.natAbs ≤ V) ∧ (s.2 ≠ 0 ∧ s.2.natAbs ≤ V))
    (v w : ℤ × ℤ) (hv : v.1 ≠ 0 ∧ v.2 ≠ 0)
    (f : ℕ → ℕ → ℝ) (hf : ∀ a b, 0 ≤ f a b) :
    ∑ s ∈ S, f (reducedModulus v.1 w.1 s.1) (reducedModulus v.2 w.2 s.2) ≤
      4 * ((v.1.natAbs.gcd w.1.natAbs).divisors.card : ℝ) *
        ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ) *
          ∑ a ∈ Finset.Icc 1 V, ∑ b ∈ Finset.Icc 1 V, f a b := by
  let A := S.image Prod.fst
  let B := S.image Prod.snd
  have hA : ∀ s ∈ A, s ≠ 0 ∧ s.natAbs ≤ V := by
    intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    exact (hS z hz).1
  have hB : ∀ s ∈ B, s ≠ 0 ∧ s.natAbs ≤ V := by
    intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    exact (hS z hz).2
  have hsub : S ⊆ A ×ˢ B := fun z hz => Finset.mem_product.mpr
    ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩, Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  calc
    _ ≤ ∑ s ∈ A ×ˢ B, f (reducedModulus v.1 w.1 s.1) (reducedModulus v.2 w.2 s.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hf _ _)
    _ = ∑ s ∈ A, ∑ t ∈ B, f (reducedModulus v.1 w.1 s) (reducedModulus v.2 w.2 t) :=
      Finset.sum_product _ _ _
    _ ≤ ∑ s ∈ A, (2 * ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ)) *
        ∑ b ∈ Finset.Icc 1 V, f (reducedModulus v.1 w.1 s) b := by
      apply Finset.sum_le_sum
      intro s hs
      exact reduced_sum_le v.2 w.2 hv.2 B V hB (f (reducedModulus v.1 w.1 s)) (hf _)
    _ = (2 * ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ)) *
        ∑ s ∈ A, ∑ b ∈ Finset.Icc 1 V, f (reducedModulus v.1 w.1 s) b := by rw [Finset.mul_sum]
    _ ≤ (2 * ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ)) *
        ((2 * ((v.1.natAbs.gcd w.1.natAbs).divisors.card : ℝ)) *
          ∑ a ∈ Finset.Icc 1 V, ∑ b ∈ Finset.Icc 1 V, f a b) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact reduced_sum_le v.1 w.1 hv.1 A V hA (fun a => ∑ b ∈ Finset.Icc 1 V, f a b)
        (fun a => Finset.sum_nonneg (fun b _ => hf a b))
    _ = _ := by ring

theorem lcm_rpow_le {V a b : ℕ} (ha : a ∈ Finset.Icc 1 V)
    (hb : b ∈ Finset.Icc 1 V) {ε : ℝ} (hε : 0 ≤ ε) :
    ((a.lcm b : ℕ) : ℝ) ^ (ε - 1) ≤ (V : ℝ) ^ (2 * ε) * ((a.lcm b : ℕ) : ℝ)⁻¹ := by
  have hl : 0 < ((a.lcm b : ℕ) : ℝ) := by
    exact_mod_cast Nat.lcm_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1
  have hle : ((a.lcm b : ℕ) : ℝ) ≤ (V : ℝ) ^ 2 := by
    have hn : a.lcm b ≤ V * V := (Nat.lcm_le_mul (Finset.mem_Icc.mp ha).1
      (Finset.mem_Icc.mp hb).1).trans (Nat.mul_le_mul (Finset.mem_Icc.mp ha).2
        (Finset.mem_Icc.mp hb).2)
    simpa only [pow_two] using (show ((a.lcm b : ℕ) : ℝ) ≤ (V : ℝ) * V by exact_mod_cast hn)
  calc
    _ = ((a.lcm b : ℕ) : ℝ) ^ ε * ((a.lcm b : ℕ) : ℝ)⁻¹ := by
      rw [Real.rpow_sub hl, Real.rpow_one, div_eq_mul_inv]
    _ ≤ ((V : ℝ) ^ 2) ^ ε * ((a.lcm b : ℕ) : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hl.le hle hε) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast (V : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg V)]
      norm_num

theorem local_sum_le (S : Finset (ℤ × ℤ)) (V : ℕ)
    (hS : ∀ s ∈ S, (s.1 ≠ 0 ∧ s.1.natAbs ≤ V) ∧ (s.2 ≠ 0 ∧ s.2.natAbs ≤ V))
    (v w : ℤ × ℤ) (hv : v.1 ≠ 0 ∧ v.2 ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ∑ s ∈ S, (modulus s v w : ℝ) ^ (ε - 1) ≤
      4 * ((v.1.natAbs.gcd w.1.natAbs).divisors.card : ℝ) *
        ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ) *
          (V : ℝ) ^ (2 * ε) * (1 + Real.log V) ^ 3 := by
  apply (paired_reduced_sum_le S V hS v w hv
    (fun a b => ((a.lcm b : ℕ) : ℝ) ^ (ε - 1)) (fun a b => by positivity)).trans
  have hsum : (∑ a ∈ Finset.Icc 1 V, ∑ b ∈ Finset.Icc 1 V,
      ((a.lcm b : ℕ) : ℝ) ^ (ε - 1)) ≤ (V : ℝ) ^ (2 * ε) * (1 + Real.log V) ^ 3 := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 V, ∑ b ∈ Finset.Icc 1 V,
          (V : ℝ) ^ (2 * ε) * ((a.lcm b : ℕ) : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.sum_le_sum (fun b hb => lcm_rpow_le ha hb hε)
      _ = (V : ℝ) ^ (2 * ε) * (∑ a ∈ Finset.Icc 1 V, ∑ b ∈ Finset.Icc 1 V,
          ((a.lcm b : ℕ) : ℝ)⁻¹) := by simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (FrequencyLCM.reciprocal_lcm_sum_le_log V) (by positivity)
  calc
    _ ≤ (4 * ((v.1.natAbs.gcd w.1.natAbs).divisors.card : ℝ) *
        ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ)) *
          ((V : ℝ) ^ (2 * ε) * (1 + Real.log V) ^ 3) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Ostmann.Arithmetic.PairedFrequencyTreeSum

end

end OAI
