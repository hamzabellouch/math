import OAI.NumberTheory.JointDickman.Amplification.TwistedBinMean
import OAI.NumberTheory.JointDickman.Analysis.MellinLowFrequencyEnergy

namespace OAI

/-! # Unconditional low-frequency energy for nonprincipal bin interpolants -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

theorem twistedBin_low_frequency
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ)
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A T ε : ℝ} (hA : 0 < A) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ τ : ℝ, |τ| ≤ T →
      ‖angularMellinPolynomial (Ioc ⌊A*x⌋₊ ⌊4*(A*x)⌋₊)
        (twistedWeightedBinInterpolant (fun i => primeBin x J (k i))
          (finitePrimeWeight P t) a χ) τ‖ ≤ ε := by
  let f := fun x : ℝ => twistedWeightedBinInterpolant (fun i => primeBin x J (k i))
    (finitePrimeWeight P t) a χ
  have hf (x : ℝ) (n : ℕ) : ‖f x n‖ ≤ 1 := by
    apply twistedWeightedBinInterpolant_norm_le _ _ _ a χ n
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds ht v).1]
    exact (finitePrimeWeight_bounds ht v).2
  apply angularMellin_uniform_bounded_frequency (fun x n => f x n)
    (by norm_num : (0 : ℝ) ≤ 1) hf (fun x => (f x).map_zero) ?_ hA hT hε
  intro B hB
  have hh := (twistedWeightedBinInterpolant_prefix_mean hJ k hk hP t ht a χ hχ hB).const_mul (B : ℂ)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  dsimp only [f]
  field_simp

theorem twistedBin_low_frequency_energy
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ)
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A T : ℝ} (hA : 0 < A) (hT : 0 ≤ T) :
    Tendsto (fun x : ℝ => ∫ τ in -T..T,
      ‖angularMellinPolynomial (Ioc ⌊A*x⌋₊ ⌊4*(A*x)⌋₊)
        (twistedWeightedBinInterpolant (fun i => primeBin x J (k i))
          (finitePrimeWeight P t) a χ) τ‖^2) atTop (𝓝 0) := by
  apply angularMellin_bounded_energy_tendsto atTop _ _ hT
  intro ε hε
  exact twistedBin_low_frequency hJ k hk hP t ht a χ hχ hA hT hε

end JointDickman

end OAI
