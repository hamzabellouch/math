import OAI.NumberTheory.EgyptianFractions.GeometricRawDensity
import OAI.NumberTheory.EgyptianFractions.DescentPolynomialLoss

namespace OAI
noncomputable section
open Filter

namespace Problem337.GeometricDensity

/-- The remaining arithmetic existence interface at a fixed scale.
It includes the actual common denominator, normalized residue lists, and
terminal residue supply. The localization loss may vary with the scale. -/
def HasSupply (DM D₀ η c r A B S : ℝ) (C : ℕ) : Prop :=
  ∃ M : ℕ, ∃ loss : ℝ,
    Nonempty (ResidueData DM D₀ η c r S loss C M) ∧
    Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (DM * S) ∧
    2 ^ TerminalDepth.binaryExponent D₀ S ∣ M ∧
    0 < loss ∧ loss ≤ A * S + B

/-- All scale, floor, geometric-depth, and localization-loss thresholds are
uniform in the original integer factor. Thus actual geometric supply is the
only arithmetic premise left in the raw density family interface. -/
theorem eventually_raw_density_supply_of_geometric
    (DM D₀ η c r A B : ℝ)
    (hDM : 1 < DM) (hD₀ : 1 ≤ D₀) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 1 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      HasSupply DM D₀ η c r A B S C →
      RawDensitySupply DM
        (TerminalAssembly.terminalCoefficient D₀ (1 - η) + 3 * (DM + 2) / η + 1)
        c (3 * (DM + 2) / η) r S C := by
  filter_upwards [ResidueLevels.eventually_scale_bounds,
    eventually_ge_atTop (1 : ℝ),
    DescentDecay.eventually_polynomial_loss_absorbed_of_le A B r hA hB hr]
    with S hscale hS hloss
  intro C hC hsupply
  obtain ⟨M, loss, ⟨H⟩, hM, hMupper, hbinary, hP, hPupper⟩ := hsupply
  have hCpos : 0 < C := by
    exact_mod_cast (Real.exp_pos (4 * (DM + 2) * S)).trans_le hC
  exact raw_density_supply_of_geometric_residues H hDM hD₀ hη hηhalf hS
    hscale.1 hscale.2.1 hscale.2.2.1 hCpos hM hMupper hbinary hP
    (hloss loss hPupper)

/-- The complete main-upper pipeline, with precisely the actual arithmetic
supply left as an explicit eventual hypothesis. No extra density or expansion
hypotheses are needed after the geometric data have been constructed. -/
theorem main_upper_of_geometric_supply
    (DM D₀ η c r A B : ℝ)
    (hDM : 1 < DM) (hD₀ : 1 ≤ D₀) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 2 ≤ r)
    (hKr : 8 * (3 * (DM + 2) / η) ≤ r)
    (hsupply : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      HasSupply DM D₀ η c r A B S C) :
    ∃ c2 : ℝ, 0 < c2 ∧ ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  have hK : 0 < 3 * (DM + 2) / η := by positivity
  have hterminal : 0 < TerminalAssembly.terminalCoefficient D₀ (1 - η) :=
    TerminalAssembly.terminalCoefficient_pos hD₀ (by linarith) (by linarith)
  apply main_upper_of_raw_density_supply DM
    (TerminalAssembly.terminalCoefficient D₀ (1 - η) + 3 * (DM + 2) / η + 1)
    c (3 * (DM + 2) / η) r hDM (by linarith) hc hK.le hr hKr
  filter_upwards [hsupply,
    eventually_raw_density_supply_of_geometric DM D₀ η c r A B hDM hD₀ hη hηhalf
      hA hB (by linarith)] with S hdata hraw
  intro C hClo hChi
  exact hraw C hClo (hdata C hClo hChi)

end Problem337.GeometricDensity

end

end OAI
