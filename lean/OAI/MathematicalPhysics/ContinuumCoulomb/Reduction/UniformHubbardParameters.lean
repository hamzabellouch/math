import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialHoppingSmallness

namespace OAI

/-! Fixed inverse-polynomial exponents close the full Hubbard-to-spin
perturbation budget for every polynomial edge count and coefficient bound. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem exists_uniform_hubbard_parameters {freq : ℝ} (hfreq : 0 < freq) (R A g : ℕ) :
    ∃ E B : ℕ, 2 ≤ E ∧ 0 < B ∧ ∀ N : ℝ, 2 ≤ N → ∀ (r : ℕ), (r : ℝ) ≤ N ^ R →
      ∀ (scale D : ℝ), 5 ≤ D → ∀ (m : ℕ) (u : Fin (m + 1) → PlanarPosition),
      (∀ i j, i ≠ j → D ≤ ‖u i - u j‖) →
      (m + 1 : ℕ) * localLeakageBound freq D ≤ localDualMass freq / 2 →
      ∀ (left right : Fin r → Fin (m + 1)) (K : Fin r → ℝ),
      (∀ e, 0 ≤ K e) → (∀ e, K e ≤ N ^ A) →
      (∀ e, left e ≠ right e) →
      (∀ e f, e ≠ f →
        ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f)) →
      (∀ e, scale * planarHopping ‖u (left e) - u (right e)‖ =
        coulombHoppingTarget freq (N ^ B)⁻¹ (K e) ‖u (left e) - u (right e)‖) →
      |HubbardGlobal.hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
          left right (fun e => scale * planarHopping ‖u (left e) - u (right e)‖) -
        HubbardGlobal.graphSourceBottom m left right (fun e => ((N ^ B)⁻¹) ^ 2 * K e)| ≤
          (N ^ g)⁻¹ * ((N ^ B)⁻¹) ^ 2 := by
  obtain ⟨L, _, hconstants⟩ := exists_polynomial_constant_bounds
    (localizedGramConstant_positive hfreq)
    (max (2 * localizedGramConstant freq) (Real.sqrt (localizedCoulombProfile freq 0)))
  let C := R + A + 2 * L + 2
  let E := g + 2 * C + L
  let B := E + C
  have hE : 2 ≤ E := by dsimp [E, C]; omega
  refine ⟨E, B, hE, by dsimp [B, E, C]; omega, ?_⟩
  intro N hN r hr scale D hD m u hsep hleak left right K hK hKhi hloop hsimple hcal
  have hNp : 0 < N := by linarith
  obtain ⟨hc, hupper⟩ := hconstants N hN
  have hc₂ : 2 * localizedGramConstant freq ≤ N ^ L := (le_max_left _ _).trans hupper
  have hU : Real.sqrt (localizedCoulombProfile freq 0) ≤ N ^ L := (le_max_right _ _).trans hupper
  have ht := polynomial_hopping_smallness hN R A L E hc hU (by simpa using hr)
    (fun e => ‖u (left e) - u (right e)‖) K hK hKhi hcal
  have hcomparison := HubbardGlobal.localized_calibrated_hubbard hfreq hD m u hsep hleak
    left right K hK hloop hsimple hcal (by positivity : 0 ≤ (N ^ E)⁻¹)
    (inverse_power_lt_half hN hE) ht
  exact hcomparison.trans (polynomial_hubbard_error_budget hNp R A L g hc₂)

end ContinuumCoulomb

end

end OAI
