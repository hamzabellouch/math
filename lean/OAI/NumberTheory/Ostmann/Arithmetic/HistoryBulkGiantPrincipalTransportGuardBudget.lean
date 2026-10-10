import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportGuard
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorExceptionalError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistoryGiantWeightedPriorReplacement PrimeCellFreezing
open ScaleBudget PrimeCellActualErrorBudget HistoryGiantReplacementError Filter
open HistoryGiantPriorExceptionalError

theorem eventually_periodic_guard_errors (k₀ : ℕ) (c₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : ℝ) (M : ℕ), 0<M →
      Real.log (M:ℝ)≤Real.exp (giant.μ*L) → Real.exp (giant.a₀*L)≤G-1 →
      ∀ (E : Finset ℕ), E.card≤2 → ∀ (hZ : 0<logCellMass G E)
      (a : ℕ), a≤residueCostExponent k₀ →
      ∀ R : ZMod M×ZMod M→ℂ, (∀z,‖R z‖≤(M:ℝ)^a) →
      (∀ f : (Bool→ℝ)→ℂ,
        (∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
          ‖f (fun i=>Real.exp (z i))‖≤ smoothGrowthFactor k₀ c₀ giant.μ L) →
        ‖guardedPeriodicSourcePrimeMean G E hZ M R f-periodicSourcePrimeMean G E hZ M R f‖≤
          Real.exp (-Real.exp (giant.target*L))) ∧
      (∀ f : (Option Unit→ℝ)→ℂ,
        (∀z∈logRectangle (Option.elim' (G-1) (fun _ : Unit=>G-1))
          (Option.elim' (G+1) (fun _ : Unit=>G+1)),
          ‖f (fun i=>Real.exp (z i))‖≤ smoothGrowthFactor k₀ c₀ giant.μ L) →
        ‖guardedPeriodicSourceMixedMean G E hZ M R f-periodicSourceMixedMean G E hZ M R f‖≤
          Real.exp (-Real.exp (giant.target*L))) := by
  filter_upwards [eventually_exceptional_errors k₀ c₀] with L hexc
  intro G M hM hmod hlo E hE hZ a ha R hR
  have hex := (hexc G M hM hmod hlo E hE).errors a
    ((M:ℝ)^a*smoothGrowthFactor k₀ c₀ giant.μ L) ha (mul_nonneg (pow_nonneg (Nat.cast_nonneg M) _) (Real.exp_nonneg _)) le_rfl
  constructor
  · intro f hf
    exact (guarded_periodic_prime_error G E hZ M R ((M:ℝ)^a) (by positivity) hR f
      (Real.exp_nonneg _) hf).trans hex.2.2.2.1
  · intro f hf
    exact (guarded_periodic_mixed_error G E hZ M R ((M:ℝ)^a) (by positivity) hR f
      (Real.exp_nonneg _) hf).trans hex.2.2.2.2

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
