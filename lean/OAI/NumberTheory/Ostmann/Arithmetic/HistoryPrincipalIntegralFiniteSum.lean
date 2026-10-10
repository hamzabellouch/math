import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralFiniteBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralFinite
open MeasureTheory Construction PrimeCellFreezing MixedCellIntegralFreezing
open HistoryPrincipalIntegralAverage
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeIntegral_finset_sum {κ : Type*} (S : Finset κ)
    (lo hi Z : ι → ℝ) (hlo : ∀ i, 0 < lo i) (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ a ∈ S, ContinuousOn (fun t => f a (fun i => Real.exp (t i))) (logRectangle lo hi)) :
    primeIntegral lo hi Z (fun x => ∑ a ∈ S, f a x) =
      ∑ a ∈ S, primeIntegral lo hi Z (f a) := by
  unfold primeIntegral logCellIntegral
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum S (fun a ha => prime_integrand_integrable lo hi Z hlo (f a) (hf a ha))

theorem mixedIntegral_finset_sum {κ : Type*} (S : Finset κ)
    (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i) (f : κ → (Option ι → ℝ) → ℂ)
    (hf : ∀ a ∈ S, ContinuousOn (fun t => f a (fun i => Real.exp (t i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    mixedIntegral loI hiI G φ lo hi Z (fun x => ∑ a ∈ S, f a x) =
      ∑ a ∈ S, mixedIntegral loI hiI G φ lo hi Z (f a) := by
  unfold mixedIntegral mixedLogIntegral
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum S (fun a ha =>
    mixed_integrand_integrable loI hiI G φ lo hi Z hφ hlo (f a) (hf a ha))

theorem primeIntegral_cmean {κ : Type*} [Fintype κ] (μ : FinitePrior κ)
    (lo hi Z : ι → ℝ) (hlo : ∀ i, 0 < lo i) (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ a, ContinuousOn (fun t => f a (fun i => Real.exp (t i))) (logRectangle lo hi)) :
    primeIntegral lo hi Z (fun x => μ.cmean (fun a => f a x)) =
      μ.cmean (fun a => primeIntegral lo hi Z (f a)) := by
  unfold FinitePrior.cmean
  rw [primeIntegral_finset_sum Finset.univ lo hi Z hlo
    (fun a x => (μ.mass a : ℂ)*f a x)
    (fun a _ => continuousOn_const.mul (hf a))]
  apply Finset.sum_congr rfl
  intro a ha
  exact primeIntegral_const_mul lo hi Z (f a) (μ.mass a : ℂ)

theorem mixedIntegral_cmean {κ : Type*} [Fintype κ] (μ : FinitePrior κ)
    (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i) (f : κ → (Option ι → ℝ) → ℂ)
    (hf : ∀ a, ContinuousOn (fun t => f a (fun i => Real.exp (t i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    mixedIntegral loI hiI G φ lo hi Z (fun x => μ.cmean (fun a => f a x)) =
      μ.cmean (fun a => mixedIntegral loI hiI G φ lo hi Z (f a)) := by
  unfold FinitePrior.cmean
  rw [mixedIntegral_finset_sum Finset.univ loI hiI G φ lo hi Z hφ hlo
    (fun a x => (μ.mass a : ℂ)*f a x)
    (fun a _ => continuousOn_const.mul (hf a))]
  apply Finset.sum_congr rfl
  intro a ha
  exact mixedIntegral_const_mul loI hiI G φ lo hi Z (f a) (μ.mass a : ℂ)

end Ostmann.Arithmetic.HistoryPrincipalIntegralFinite

end

end OAI
