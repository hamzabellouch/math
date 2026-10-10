import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsBulk
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsGiant
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsMixed
import OAI.NumberTheory.Ostmann.Construction.LogCellPrimePrior

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralBounds
open Filter Construction PrimeCellFreezing HistoryPrincipalIntegralAverage HistoryGiantPriorGrid

theorem eventually_norm_giant_integrals_le :
    ∀ᶠ G : ℝ in atTop, ∀ E : Finset ℕ, E.card ≤ 2 →
      0 < Construction.logCellMass G E ∧
      (∀ {A : ℝ}, 0 ≤ A → ∀ f : (Bool → ℝ) → ℂ,
        (∀ t ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
          ‖f (fun i => Real.exp (t i))‖ ≤ A) →
        ‖primeIntegral (fun _ : Bool => G-1) (fun _ => G+1)
          (fun _ => Construction.logCellMass G E) (primeCutoff G f)‖ ≤ 64*A) ∧
      (∀ {A : ℝ}, 0 ≤ A → ∀ f : (Option Unit → ℝ) → ℂ,
        (∀ t ∈ logRectangle (fun _ : Option Unit => G-1) (fun _ => G+1),
          ‖f (fun i => Real.exp (t i))‖ ≤ A) →
        ‖mixedIntegral (G-1) (G+1) G smoothPartition (fun _ : Unit => G-1) (fun _ => G+1)
          (fun _ => Construction.logCellMass G E) (mixedGiantPrimeTest G f)‖ ≤ 16*Real.exp 1*A) := by
  filter_upwards [logCell_normalization_eventually,eventually_ge_atTop (2 : ℝ)] with G hn hG
  intro E hE
  obtain ⟨hZ,_,hZi⟩ := hn E hE
  exact ⟨hZ,fun hA f hf => norm_prime_giantIntegral_le hG hZ hZi hA f hf,
    fun hA f hf => norm_mixed_giantIntegral_le hG hZ hZi hA f hf⟩

end Ostmann.Arithmetic.HistoryPrincipalIntegralBounds

end

end OAI
