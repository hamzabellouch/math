import OAI.NumberTheory.JointDickman.Counting.ComplexCoefficientLaw
import OAI.NumberTheory.JointDickman.Probability.UnitResidueSum

namespace OAI

/-! # Coefficient estimates against bounded periodic phases -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

theorem coefficientWeight_isUnit {B q n : ℕ} [NeZero q]
    (hq : q ≤ auxiliaryCutoff B) (hn : coefficientWeight B n ≠ 0) :
    IsUnit (n : ZMod q) := by
  apply (ZMod.isUnit_iff_coprime n q).mpr
  apply roughSquarefreeWeight_coprime (NeZero.ne q) hq (1 / 2)
  exact (mul_ne_zero_iff.mp hn).2

open Classical in
/-- Summing unit progressions costs at most the modulus. The bounded
periodic phase is arbitrary, so additive phases are included. -/
theorem coefficient_periodic_smooth_test
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b : ℝ, 9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ ψ : ZMod q → ℂ, (∀ r : (ZMod q)ˣ, ‖ψ r‖ ≤ 1) →
      ∀ φ φ' : ℝ → ℂ, ∀ M N : ℝ, 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M) → (∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N) →
      ‖(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ψ (n : ZMod q) *
          (φ n * (coefficientWeight B n : ℂ))) -
        (∑ r : (ZMod q)ˣ, ψ r) *
          ((∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
            (q.totient : ℂ))‖ ≤
        (q : ℝ) * (K * (B : ℝ) ^ (-D) * b * (2 * M + N * (b - a))) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := coefficientProgression_complex_test hSD hSW hM hD
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro a b ha hab hloga q _ hq ψ hψ φ φ' M N hM0 hN hφ hφ' hvalue hderiv
  have hBP : (B : ℝ) ^ (100 : ℝ) ≤ auxiliaryCutoff B := by
    calc
      (B : ℝ) ^ (100 : ℝ) = (B : ℝ) ^ (100 : ℕ) := by norm_num
      _ ≤ (B : ℝ) ^ (1000 : ℕ) :=
        pow_le_pow_right₀ (by exact_mod_cast hB) (by omega)
      _ = auxiliaryCutoff B := by simp only [auxiliaryCutoff, Nat.cast_pow]
  have hqP : q ≤ auxiliaryCutoff B := by exact_mod_cast hq.trans hBP
  have hunit : ∀ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
      φ n * (coefficientWeight B n : ℂ) ≠ 0 → IsUnit (n : ZMod q) := by
    intro n _ hn
    apply coefficientWeight_isUnit hqP
    intro hz
    simp only [hz, Complex.ofReal_zero, mul_zero, ne_eq, not_true_eq_false] at hn
  have hest := sum_unit_residue_error (Ioc ⌊a⌋₊ ⌊b⌋₊)
    (fun n => φ n * (coefficientWeight B n : ℂ)) ψ
    ((∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
      (q.totient : ℂ)) hunit hψ
    (fun r => hboundB a b ha hab hloga q hq r φ φ' M N hM0 hN hφ hφ' hvalue hderiv)
  refine hest.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q) ?_)
  exact mul_nonneg (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg B) _))
    (by linarith)) (add_nonneg (by positivity) (mul_nonneg hN (sub_nonneg.mpr hab)))

end JointDickman

end OAI
