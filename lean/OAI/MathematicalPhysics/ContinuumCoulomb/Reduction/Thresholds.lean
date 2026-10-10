import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Promise transfer for continuum Coulomb energy

The numerical energy comparisons give rational threshold maps preserving
both source promises and an output threshold gap of at least one.
-/

namespace ContinuumCoulomb

/-- The rational affine thresholds in 271-01, §6, equations
`rounded-affine-error` and `output-gap`, preserve the source promises. -/
theorem binary_threshold_transfer
    {sourceEnergy physicalEnergy sourceYes sourceNo slope offset : ℝ}
    (hslope : 0 < slope) (hgap : sourceYes < sourceNo)
    (herror : |physicalEnergy - (slope * sourceEnergy + offset)| ≤
      (5 / 64 : ℝ) * slope * (sourceNo - sourceYes)) :
    (sourceEnergy ≤ sourceYes →
      physicalEnergy < slope * (sourceYes + (sourceNo - sourceYes) / 4) + offset) ∧
    (sourceNo ≤ sourceEnergy →
      slope * (sourceNo - (sourceNo - sourceYes) / 4) + offset < physicalEnergy) := by
  obtain ⟨hlower, hupper⟩ := abs_le.mp herror
  have hscale : 0 < slope * (sourceNo - sourceYes) :=
    mul_pos hslope (sub_pos.mpr hgap)
  constructor
  · intro hyes
    have hmono := mul_le_mul_of_nonneg_left hyes hslope.le
    nlinarith
  · intro hno
    have hmono := mul_le_mul_of_nonneg_left hno hslope.le
    nlinarith

/-- The binary-charge output loses exactly half of the scaled source gap. -/
theorem binary_output_gap (sourceYes sourceNo slope offset : ℝ) :
    (slope * (sourceNo - (sourceNo - sourceYes) / 4) + offset) -
      (slope * (sourceYes + (sourceNo - sourceYes) / 4) + offset) =
        slope * (sourceNo - sourceYes) / 2 := by
  ring

/-- The unit-charge manuscript, §7, equation (10): the energy error and
rounding errors have distinct budgets. The thresholds may be any rational
approximations satisfying the stated real error bounds. -/
theorem unit_threshold_transfer
    {sourceEnergy physicalEnergy sourceYes sourceNo slope offset gamma
      outputYes outputNo : ℝ}
    (hslope : 0 < slope) (hgamma : 0 < gamma)
    (hgap : gamma ≤ sourceNo - sourceYes)
    (herror : |physicalEnergy - (slope * sourceEnergy + offset)| ≤
      slope * gamma / 8)
    (hroundYes : |outputYes - (slope * (sourceYes + gamma / 4) + offset)| ≤
      slope * gamma / 32)
    (hroundNo : |outputNo - (slope * (sourceNo - gamma / 4) + offset)| ≤
      slope * gamma / 32) :
    (sourceEnergy ≤ sourceYes → physicalEnergy < outputYes) ∧
    (sourceNo ≤ sourceEnergy → outputNo < physicalEnergy) ∧
    (7 / 16 : ℝ) * slope * gamma ≤ outputNo - outputYes := by
  obtain ⟨hel, heu⟩ := abs_le.mp herror
  obtain ⟨hal, hau⟩ := abs_le.mp hroundYes
  obtain ⟨hbl, hbu⟩ := abs_le.mp hroundNo
  have hscale : 0 < slope * gamma := mul_pos hslope hgamma
  have hscaledGap := mul_le_mul_of_nonneg_left hgap hslope.le
  refine ⟨?_, ?_, ?_⟩
  · intro hyes
    have hmono := mul_le_mul_of_nonneg_left hyes hslope.le
    nlinarith
  · intro hno
    have hmono := mul_le_mul_of_nonneg_left hno hslope.le
    nlinarith
  · nlinarith

/-- The unit-charge construction requests scaled gap at least eight. -/
theorem unit_output_gap_at_least_one {slope gamma outputYes outputNo : ℝ}
    (hscale : 8 ≤ slope * gamma)
    (hgap : (7 / 16 : ℝ) * slope * gamma ≤ outputNo - outputYes) :
    1 ≤ outputNo - outputYes := by
  nlinarith

/-- An output threshold gap at least one meets precision exponent `c = 1`
for every positive total input length; there is no circular size estimate. -/
theorem inverse_length_precision {outputYes outputNo : ℝ} {length : ℕ}
    (hlength : 1 ≤ length) (hgap : 1 ≤ outputNo - outputYes) :
    (length : ℝ)⁻¹ ≤ outputNo - outputYes := by
  have hlength' : (1 : ℝ) ≤ length := by exact_mod_cast hlength
  have hinv : (length : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hlength')).2 hlength'
  exact hinv.trans hgap

end ContinuumCoulomb

end OAI
