import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverageMixed
import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralFinite
open MeasureTheory Construction PrimeCellFreezing MixedCellIntegralFreezing
open HistoryPrincipalIntegralAverage
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem prime_integrand_integrable [_decidableEqIndex : DecidableEq ι]
    (lo hi Z : ι → ℝ) (hlo : ∀ i, 0 < lo i)
    (f : (ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun t => f (fun i => Real.exp (t i))) (logRectangle lo hi)) :
    IntegrableOn (fun t => logCellDensity (fun i => (Z i)⁻¹) t •
      f (fun i => Real.exp (t i))) (logRectangle lo hi) :=
  ((continuousOn_logCellDensity _ lo hi hlo).smul hf).integrableOn_compact
    (isCompact_logRectangle lo hi)

omit [Fintype ι] [DecidableEq ι] in
theorem mixed_test_continuous [_fintypeIndex : Fintype ι] [_decidableEqIndex : DecidableEq ι]
    (loI hiI : ℝ) (lo hi : ι → ℝ)
    (f : (Option ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun t => f (fun i => Real.exp (t i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    ContinuousOn (fun t => f (optionCoordinates (mixedExp t)))
      (mixedLogRectangle loI hiI lo hi) := by
  have hh := hf.comp continuous_optionCoordinates.continuousOn
    (fun t ht => (optionCoordinates_mem_logRectangle loI hiI lo hi).mpr ht)
  simpa only [Function.comp_def,optionCoordinates_mixedExp] using hh

theorem mixed_integrand_integrable (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (lo hi Z : ι → ℝ) (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i)
    (f : (Option ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun t => f (fun i => Real.exp (t i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    IntegrableOn (fun t => mixedLogDensity 1 G φ (fun i => (Z i)⁻¹) t •
      f (optionCoordinates (mixedExp t))) (mixedLogRectangle loI hiI lo hi) :=
  ((continuousOn_mixedLogDensity 1 loI hiI G φ _ lo hi hφ hlo).smul
    (mixed_test_continuous loI hiI lo hi f hf)).integrableOn_compact
      (isCompact_mixedLogRectangle loI hiI lo hi)

omit [DecidableEq ι] in

theorem primeIntegral_const_mul (lo hi Z : ι → ℝ) (f : (ι → ℝ) → ℂ) (c : ℂ) :
    primeIntegral lo hi Z (fun x => c*f x) = c*primeIntegral lo hi Z f := by
  unfold primeIntegral logCellIntegral
  have he : (fun t => logCellDensity (fun i => (Z i)⁻¹) t •
      (c*f (fun i => Real.exp (t i)))) =
      (fun t => c*(logCellDensity (fun i => (Z i)⁻¹) t • f (fun i => Real.exp (t i)))) := by
    funext t
    simp only [Complex.real_smul]
    ring
  rw [he,integral_const_mul]

omit [DecidableEq ι] in

theorem mixedIntegral_const_mul (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (lo hi Z : ι → ℝ) (f : (Option ι → ℝ) → ℂ) (c : ℂ) :
    mixedIntegral loI hiI G φ lo hi Z (fun x => c*f x) =
      c*mixedIntegral loI hiI G φ lo hi Z f := by
  unfold mixedIntegral mixedLogIntegral
  have he : (fun t => mixedLogDensity 1 G φ (fun i => (Z i)⁻¹) t •
      (c*f (optionCoordinates (mixedExp t)))) =
      (fun t => c*(mixedLogDensity 1 G φ (fun i => (Z i)⁻¹) t •
        f (optionCoordinates (mixedExp t)))) := by
    funext t
    simp only [Complex.real_smul]
    ring
  rw [he,integral_const_mul]

end Ostmann.Arithmetic.HistoryPrincipalIntegralFinite

end

end OAI
