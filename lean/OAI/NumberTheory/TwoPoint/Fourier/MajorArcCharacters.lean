import OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

namespace OAI

/-! Multiplicative Fourier resolution of the reduced, unit progression in
MRT section 4. The original residue need not be a unit: this lemma is applied
after taking out its common divisor with the modulus. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma major_arc_unit_indicator (q : ℕ) [NeZero q] (b : ZMod q)
    (hb : IsUnit b) (n : ZMod q) :
    (if n = b then (1 : ℂ) else 0) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ b⁻¹ * χ n := by
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb n]
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  by_cases h : n = b
  · simp [h, hφ]
  · simp [h, Ne.symm h]

lemma major_arc_unit_progression (S : Finset ℕ) (v : ℕ → ℂ)
    (q : ℕ) [NeZero q] (b : ZMod q) (hb : IsUnit b) :
    (∑ n ∈ S, if (n : ZMod q) = b then v n else 0) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ b⁻¹ * ∑ n ∈ S, v n * χ (n : ZMod q) := by
  have hi (n : ℕ) : (if (n : ZMod q) = b then v n else 0) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ b⁻¹ * (v n * χ (n : ZMod q)) := by
    have h := congrArg (fun z : ℂ => z * v n)
      (major_arc_unit_indicator q b hb (n : ZMod q))
    simp only [ite_mul, one_mul, zero_mul] at h
    rw [h, mul_assoc, sum_mul]
    congr 1
    apply sum_congr rfl
    intro χ _
    ring
  simp_rw [hi]
  rw [← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl
  intro χ _
  rw [mul_sum]

lemma major_arc_unit_progression_norm (S : Finset ℕ) (v : ℕ → ℂ)
    (q : ℕ) [NeZero q] (b : ZMod q) (hb : IsUnit b) :
    ‖∑ n ∈ S, if (n : ZMod q) = b then v n else 0‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ‖∑ n ∈ S, v n * χ (n : ZMod q)‖ := by
  rw [major_arc_unit_progression S v q b hb, norm_mul, norm_inv,
    Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro χ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

lemma major_arc_typical_twist {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    mrtTypicalCoefficient J P (twistByCharacter F χ) =
      twistByCharacter (mrtTypicalCoefficient J P F) χ := by
  funext n
  simp only [mrtTypicalCoefficient, twistByCharacter]
  split_ifs <;> simp

end TwoPointCorrelations

end OAI
