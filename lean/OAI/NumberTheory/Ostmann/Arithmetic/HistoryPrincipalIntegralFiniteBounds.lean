import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralFiniteSum

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralFinite
open MeasureTheory Construction PrimeCellFreezing MixedCellIntegralFreezing
open HistoryPrincipalIntegralAverage HistoryPrincipalIntegralBounds
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeIntegral_sub (lo hi Z : ι → ℝ) (hlo : ∀ i, 0 < lo i)
    (f g : (ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun t => f (fun i => Real.exp (t i))) (logRectangle lo hi))
    (hg : ContinuousOn (fun t => g (fun i => Real.exp (t i))) (logRectangle lo hi)) :
    primeIntegral lo hi Z (fun x => f x-g x) =
      primeIntegral lo hi Z f-primeIntegral lo hi Z g := by
  unfold primeIntegral logCellIntegral
  simp_rw [smul_sub]
  exact integral_sub (prime_integrand_integrable lo hi Z hlo f hf)
    (prime_integrand_integrable lo hi Z hlo g hg)

theorem mixedIntegral_sub (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i) (f g : (Option ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun t => f (fun i => Real.exp (t i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi)))
    (hg : ContinuousOn (fun t => g (fun i => Real.exp (t i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    mixedIntegral loI hiI G φ lo hi Z (fun x => f x-g x) =
      mixedIntegral loI hiI G φ lo hi Z f-mixedIntegral loI hiI G φ lo hi Z g := by
  unfold mixedIntegral mixedLogIntegral
  simp_rw [smul_sub]
  exact integral_sub (mixed_integrand_integrable loI hiI G φ lo hi Z hφ hlo f hf)
    (mixed_integrand_integrable loI hiI G φ lo hi Z hφ hlo g hg)

omit [DecidableEq ι] in
theorem mixedIntegral_norm_le_mass (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (hφ : Continuous φ) (hφ0 : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hlo : ∀ i, 0 < lo i) (hZ : ∀ i, 0 < Z i)
    (f : (Option ι → ℝ) → ℂ) {ε : ℝ}
    (hf : ∀ t ∈ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi),
      ‖f (fun i => Real.exp (t i))‖ ≤ ε) :
    ‖mixedIntegral loI hiI G φ lo hi Z f‖ ≤
      ε*mixedLogMass 1 loI hiI G φ (fun i => (Z i)⁻¹) lo hi := by
  have hcompact := isCompact_mixedLogRectangle loI hiI lo hi
  have hdi := integrableOn_mixedLogDensity 1 loI hiI G φ (fun i => (Z i)⁻¹) lo hi hφ hlo
  unfold mixedIntegral mixedLogIntegral
  calc
    _ ≤ ∫ t in mixedLogRectangle loI hiI lo hi,
        mixedLogDensity 1 G φ (fun i => (Z i)⁻¹) t*ε := by
      apply norm_integral_le_of_norm_le (hdi.mul_const ε)
      filter_upwards [ae_restrict_mem hcompact.measurableSet] with t ht
      have hn := mixedLogDensity_nonneg 1 loI hiI G φ (fun i => (Z i)⁻¹) lo hi
        hφ0 (fun i => inv_nonneg.mpr (hZ i).le) hlo ht
      have htest := hf (optionCoordinates t)
        ((optionCoordinates_mem_logRectangle loI hiI lo hi).mpr ht)
      rw [← optionCoordinates_mixedExp] at htest
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left htest hn
    _ = _ := by
      rw [integral_mul_const]
      exact mul_comm _ _

theorem primeIntegral_difference_le_mass (lo hi Z : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (hZ : ∀ i, 0 < Z i) (f g : (ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun t => f (fun i => Real.exp (t i))) (logRectangle lo hi))
    (hg : ContinuousOn (fun t => g (fun i => Real.exp (t i))) (logRectangle lo hi))
    {ε : ℝ} (he : ∀ t ∈ logRectangle lo hi,
      ‖f (fun i => Real.exp (t i))-g (fun i => Real.exp (t i))‖ ≤ ε) :
    ‖primeIntegral lo hi Z f-primeIntegral lo hi Z g‖ ≤
      ε*PrimeCellFreezing.logCellMass (fun i => (Z i)⁻¹) lo hi := by
  rw [← primeIntegral_sub lo hi Z hlo f g hf hg]
  exact primeIntegral_norm_le_mass lo hi Z hlo hZ (fun x => f x-g x) he

theorem mixedIntegral_difference_le_mass (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (hφ : Continuous φ) (hφ0 : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hlo : ∀ i, 0 < lo i) (hZ : ∀ i, 0 < Z i) (f g : (Option ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun t => f (fun i => Real.exp (t i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi)))
    (hg : ContinuousOn (fun t => g (fun i => Real.exp (t i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi)))
    {ε : ℝ} (he : ∀ t ∈ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi),
      ‖f (fun i => Real.exp (t i))-g (fun i => Real.exp (t i))‖ ≤ ε) :
    ‖mixedIntegral loI hiI G φ lo hi Z f-mixedIntegral loI hiI G φ lo hi Z g‖ ≤
      ε*mixedLogMass 1 loI hiI G φ (fun i => (Z i)⁻¹) lo hi := by
  rw [← mixedIntegral_sub loI hiI G φ lo hi Z hφ hlo f g hf hg]
  exact mixedIntegral_norm_le_mass loI hiI G φ lo hi Z hφ hφ0 hlo hZ (fun x => f x-g x) he

end Ostmann.Arithmetic.HistoryPrincipalIntegralFinite

end

end OAI
