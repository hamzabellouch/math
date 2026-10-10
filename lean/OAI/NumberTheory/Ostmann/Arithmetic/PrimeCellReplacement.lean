import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open scoped BigOperators
open PrimeProgression

def residueMass (N M : ℕ) (a : ZMod M) (lo hi Z : ℝ) : ℝ :=
  ∑ p ∈ (logPrimeSupport N lo hi).filter (fun p : ℕ => (p : ZMod M) = a),
    (Z * (p : ℝ))⁻¹

theorem residueMass_eq (N M : ℕ) (a : ZMod M) (lo hi Z : ℝ) :
    residueMass N M a lo hi Z = harmonicProgression N M a lo hi / Z := by
  simp only [residueMass, harmonicProgression, mul_inv_rev, div_eq_mul_inv, Finset.sum_mul]

theorem residueMass_nonneg (N M : ℕ) (a : ZMod M) (lo hi : ℝ) {Z : ℝ}
    (hZ : 0 ≤ Z) : 0 ≤ residueMass N M a lo hi Z := by
  unfold residueMass
  exact Finset.sum_nonneg fun p _ => inv_nonneg.mpr (mul_nonneg hZ (Nat.cast_nonneg p))

theorem residueMass_error_of_harmonic_error (N M : ℕ) (a : ZMod M)
    (lo hi : ℝ) {Z E : ℝ} (hZ : 0 < Z)
    (h : |harmonicProgression N M a lo hi - harmonicIntegral M lo hi| ≤ E) :
    |residueMass N M a lo hi Z - harmonicIntegral M lo hi / Z| ≤ E / Z := by
  rw [residueMass_eq, ← sub_div, abs_div, abs_of_pos hZ]
  exact div_le_div_of_nonneg_right h hZ.le

theorem exists_residueMass_error_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧ ∀ lo hi : ℝ,
      L₀ ≤ lo → lo ≤ hi → hi-lo ≤ 1 → ∀ (N M : ℕ) (a : ZMod M) (Z : ℝ),
      ⌊Real.exp hi⌋₊ ≤ N → 0 < M → IsUnit a → 0 < Z →
      (M : ℝ) ≤ Real.exp (d * lo ^ (1/3 : ℝ)) →
      |residueMass N M a lo hi Z - harmonicIntegral M lo hi / Z| ≤
        (K/Z) * Real.exp (-d * lo ^ (1/3 : ℝ)) := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,h⟩ := exists_harmonicProgression_error_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro lo hi hlo hlohi hlen N M a Z hN hM ha hZ hmod
  have he := residueMass_error_of_harmonic_error N M a lo hi hZ
    (h lo hi hlo hlohi hlen N M a hN hM ha hmod)
  convert he using 1; ring

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
