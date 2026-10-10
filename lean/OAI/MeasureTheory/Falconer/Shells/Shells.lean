import OAI.MeasureTheory.Falconer.Measures.TotalVariation
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Linarith

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set ComplexConjugate
open scoped ENNReal

theorem source_fourier_convention (μ : Measure ℝ) (r : ℝ) :
    charFun μ r = ∫ s, Complex.exp ((r : ℂ)*(s : ℂ)*Complex.I) ∂μ :=
  charFun_apply_real r

noncomputable def dyadicShell (N : ℕ) : Set ℝ :=
  {r | (2 : ℝ)^((N : ℝ)-1) ≤ |r| ∧ |r| ≤ (2 : ℝ)^((N : ℝ)+1)}

theorem dyadicShell_compact (N : ℕ) : IsCompact (dyadicShell N) := by
  have hc : IsClosed (dyadicShell N) :=
    (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro r hr
  exact abs_le.mp hr.2

theorem shell_energy_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (N : ℕ) :
    IntegrableOn (fun r => ‖charFun μ r‖^2) (dyadicShell N) volume := by
  exact ((continuous_charFun.norm.pow 2).continuousOn).integrableOn_compact
    (dyadicShell_compact N)

noncomputable def shellEnergy (μ : Measure ℝ) (N : ℕ) : ℝ :=
  ∫ r in dyadicShell N, ‖charFun μ r‖^2

theorem shellEnergy_nonneg (μ : Measure ℝ) (N : ℕ) : 0 ≤ shellEnergy μ N :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem fourier_energy_even (μ : Measure ℝ) (r : ℝ) :
    ‖charFun μ (-r)‖^2 = ‖charFun μ r‖^2 := by
  rw [charFun_neg]
  simp

theorem charFun_add_measure (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (r : ℝ) : charFun (μ+ν) r = charFun μ r+charFun ν r := by
  simp only [charFun_eq_integral_innerProbChar]
  exact integral_add_measure ((BoundedContinuousFunction.innerProbChar r).integrable μ)
    ((BoundedContinuousFunction.innerProbChar r).integrable ν)

theorem fourier_sub_le_removed_mass (τ σ ρ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] [IsFiniteMeasure ρ]
    (h : τ = σ+ρ) (r : ℝ) : ‖charFun τ r-charFun σ r‖ ≤ ρ.real univ := by
  rw [h,charFun_add_measure,add_sub_cancel_left]
  exact norm_charFun_le r

noncomputable def variationDistance (τ σ : FiniteMeasure ℝ) : ℝ≥0∞ :=
  ((τ : Measure ℝ).toSignedMeasure-(σ : Measure ℝ).toSignedMeasure).totalVariation univ

def HasShellApproximations (τ : FiniteMeasure ℝ) : Prop :=
  ∃ τN : ℕ → FiniteMeasure ℝ, ∃ η γ Ctv Cshell : ℝ,
    0 < η ∧ 0 < γ ∧ 0 < Ctv ∧ 0 < Cshell ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      variationDistance τ (τN N) ≤ ENNReal.ofReal (Ctv*(2 : ℝ)^(-η*(N : ℝ))) ∧
      shellEnergy (τN N) N ≤ Cshell*(2 : ℝ)^(-γ*(N : ℝ))

def ShellCriterionTarget : Prop :=
  ∀ τ : FiniteMeasure ℝ, HasShellApproximations τ → (τ : Measure ℝ) ≪ volume

end PlanarFalconer

end OAI
