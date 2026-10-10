import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralParameterBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralParameter
open MeasureTheory Set PrimeCellFreezing MixedCellIntegralFreezing
open HistoryPrincipalIntegralAverage
variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem primeIntegral_continuousOn [DecidableEq ι] {S : Set P} (hS : IsCompact S)
    (lo hi Z : ι → ℝ) (hlo : ∀ i, 0 < lo i) (f : P → (ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun z : P × (ι → ℝ) => f z.1 (fun i => Real.exp (z.2 i)))
      (S ×ˢ logRectangle lo hi)) :
    ContinuousOn (fun p => primeIntegral lo hi Z (f p)) S := by
  unfold primeIntegral logCellIntegral
  apply continuousOn_setIntegral_compact hS (isCompact_logRectangle lo hi)
  have hden : ContinuousOn (fun z : P × (ι → ℝ) => logCellDensity (fun i => (Z i)⁻¹) z.2)
      (S ×ˢ logRectangle lo hi) := (continuousOn_logCellDensity (fun i => (Z i)⁻¹) lo hi hlo).comp
    continuous_snd.continuousOn (fun z hz => hz.2)
  exact hden.smul hf

omit [FirstCountableTopology P] [Fintype ι] [DecidableEq ι] in
theorem mixed_test_joint_continuousOn [FirstCountableTopology P] [Fintype ι] [DecidableEq ι]
    {S : Set P}
    (loI hiI : ℝ) (lo hi : ι → ℝ) (f : P → (Option ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun z : P × (Option ι → ℝ) => f z.1 (fun i => Real.exp (z.2 i)))
      (S ×ˢ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    ContinuousOn (fun z : P × (ℝ × (ι → ℝ)) => f z.1 (optionCoordinates (mixedExp z.2)))
      (S ×ˢ mixedLogRectangle loI hiI lo hi) := by
  have hh : ContinuousOn (fun z : P × (ℝ × (ι → ℝ)) =>
      f z.1 (fun i => Real.exp (optionCoordinates z.2 i)))
      (S ×ˢ mixedLogRectangle loI hiI lo hi) := hf.comp
    (continuous_fst.prodMk (continuous_optionCoordinates.comp continuous_snd)).continuousOn
    (fun z hz => ⟨hz.1,(optionCoordinates_mem_logRectangle loI hiI lo hi).mpr hz.2⟩)
  simpa only [Function.comp_def,optionCoordinates_mixedExp] using hh

theorem mixedIntegral_continuousOn {S : Set P} (hS : IsCompact S)
    (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i)
    (f : P → (Option ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun z : P × (Option ι → ℝ) => f z.1 (fun i => Real.exp (z.2 i)))
      (S ×ˢ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    ContinuousOn (fun p => mixedIntegral loI hiI G φ lo hi Z (f p)) S := by
  unfold mixedIntegral mixedLogIntegral
  apply continuousOn_setIntegral_compact hS (isCompact_mixedLogRectangle loI hiI lo hi)
  have hden : ContinuousOn (fun z : P × (ℝ × (ι → ℝ)) =>
      mixedLogDensity 1 G φ (fun i => (Z i)⁻¹) z.2)
      (S ×ˢ mixedLogRectangle loI hiI lo hi) := (continuousOn_mixedLogDensity 1 loI hiI G φ (fun i => (Z i)⁻¹)
    lo hi hφ hlo).comp continuous_snd.continuousOn (fun z hz => hz.2)
  exact hden.smul (mixed_test_joint_continuousOn loI hiI lo hi f hf)

end Ostmann.Arithmetic.HistoryPrincipalIntegralParameter

end

end OAI
