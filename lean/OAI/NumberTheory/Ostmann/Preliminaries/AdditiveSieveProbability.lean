import OAI.NumberTheory.Ostmann.Preliminaries.PublishedAdditiveSieve
import OAI.NumberTheory.Ostmann.Supply.NaturalResidueAverage

namespace OAI

/-! # The additive large sieve for a uniform measure on an actual interval subset -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def intervalSetExponentialSum {M : ℕ} (A : Finset (Fin M))
    (J : ℤ) (q h : ℕ) : ℂ :=
  ∑ n ∈ A, sieveAdditivePhase q h (J + (n.val : ℤ))

noncomputable def intervalSetReducedEnergy {M : ℕ} (A : Finset (Fin M))
    (J : ℤ) (q : ℕ) : ℝ :=
  ∑ h ∈ reducedNumerators q,
    ‖(A.card : ℂ)⁻¹ * intervalSetExponentialSum A J q h‖ ^ 2

theorem intervalSetReducedEnergy_nonneg {M : ℕ} (A : Finset (Fin M))
    (J : ℤ) (q : ℕ) : 0 ≤ intervalSetReducedEnergy A J q := by
  exact Finset.sum_nonneg (fun h _ => sq_nonneg _)

/-- No density or distribution assumption on the interval subset is needed. -/
theorem additiveSieve_probability_bound (ls : PublishedAdditiveLargeSieve)
    {M Q : ℕ} (hM : 1 ≤ M) (hQ : 1 ≤ Q) (A : Finset (Fin M))
    (hA : A.Nonempty) (J : ℤ) :
    (∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  let c : Fin M → ℂ := fun n => if n ∈ A then 1 else 0
  have hc (q h : ℕ) : additiveSieveSum c J q h = intervalSetExponentialSum A J q h := by
    simp [additiveSieveSum, intervalSetExponentialSum, c]
  have hn : (∑ n, ‖c n‖ ^ 2) = (A.card : ℝ) := by
    have he (n : Fin M) : ‖c n‖ ^ 2 = if n ∈ A then (1 : ℝ) else 0 := by
      by_cases h : n ∈ A <;> simp [c, h]
    simp [he]
  have hh := ls M Q hM hQ J c
  simp only [hc, hn] at hh
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  calc
    _ = ((A.card : ℝ)⁻¹) ^ 2 *
        ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q,
          ‖intervalSetExponentialSum A J q h‖ ^ 2 := by
      simp only [intervalSetReducedEnergy, norm_mul, norm_inv, Complex.norm_natCast,
        mul_pow, Finset.mul_sum]
    _ ≤ ((A.card : ℝ)⁻¹) ^ 2 * (((M : ℝ) + (Q : ℝ) ^ 2) * A.card) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by field_simp

theorem sieveAdditivePhase_eq_stdAddChar (q : ℕ) [NeZero q] (h : ℕ) (n : ℤ) :
    sieveAdditivePhase q h n = ZMod.stdAddChar ((h : ZMod q) * (n : ZMod q)) := by
  have hh : (h : ZMod q) * (n : ZMod q) = (((h : ℤ) * n : ℤ) : ZMod q) := by
    push_cast
    rfl
  rw [hh, ZMod.stdAddChar_coe]
  unfold sieveAdditivePhase
  congr 1
  push_cast
  ring

end Ostmann

end OAI
