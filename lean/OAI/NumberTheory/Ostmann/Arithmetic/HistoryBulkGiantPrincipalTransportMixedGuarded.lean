import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportGuardBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportMixedCore
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverage

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction Conclusion Filter ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget
open HistoryGiantWeightedPriorReplacement HistoryGiantGridCellBounds HistoryGiantReplacementGeometry
open HistoryGiantReplacementError HistoryPrincipalIntegralAverage HistoryCRTIntegration ResidueHaar
open PrimeCellReplacement PrimeCellFreezing LogCellPartition HistoryGiantPriorGrid
open HistoryPairSmoothXi

theorem exists_guarded_periodic_mixed_replacement_core :
    ∃ δ K L₀ : ℝ, 0<δ ∧ 0<K ∧ 1≤L₀ ∧
    ∀ (k₀ : ℕ) (c₀ : ℝ), ∀ᶠ L : ℝ in atTop,
    ∀ (G : ℝ) (M : ℕ) [NeZero M] (deleted : Finset ℕ) (hZ : 0<logCellMass G deleted),
      deleted.card≤2 → Real.log (M:ℝ)≤Real.exp (giant.μ*L) →
      Real.exp (giant.a₀*L)≤G-1 →
      GeometryBounds δ L₀ G M L → PrimeBounds k₀ δ K L₀ G L M deleted →
    ∀ (a : ℕ), a≤residueCostExponent k₀ →
    ∀ (R : ZMod M×ZMod M→ℂ), (∀z,‖R z‖≤(M:ℝ)^a) →
      (∑r : ZMod M,∑u : Unit→(ZMod M)ˣ,‖mixedTest R r u‖)≤(M:ℝ)^a →
    ∀ (f : (Option Unit→ℝ)→ℂ),
      (∀z∈logRectangle (Option.elim' (G-1) (fun _ : Unit=>G-1))
          (Option.elim' (G+1) (fun _ : Unit=>G+1)),
        DifferentiableAt ℝ (fun y=>mixedGiantPrimeTest G f (fun i=>Real.exp (y i))) z) →
      (∀z∈logRectangle (Option.elim' (G-1) (fun _ : Unit=>G-1))
          (Option.elim' (G+1) (fun _ : Unit=>G+1)),∀i,
        ‖deriv (fun t=>mixedGiantPrimeTest G f
          (Characters.RationalHistory.Expr.logCurve (fun q=>Real.exp (z q)) i t)) 0‖≤
          smoothGrowthFactor k₀ c₀ giant.μ L) →
      (∀z∈logRectangle (Option.elim' (G-1) (fun _ : Unit=>G-1))
          (Option.elim' (G+1) (fun _ : Unit=>G+1)),
        ‖mixedGiantPrimeTest G f (fun i=>Real.exp (z i))‖≤ smoothGrowthFactor k₀ c₀ giant.μ L) →
      (∀z∈logRectangle (Option.elim' (G-1) (fun _ : Unit=>G-1))
          (Option.elim' (G+1) (fun _ : Unit=>G+1)),
        ‖f (fun i=>Real.exp (z i))‖≤ smoothGrowthFactor k₀ c₀ giant.μ L) →
      ‖guardedPeriodicSourceMixedMean G deleted hZ M R f-
        mixedIntegral (G-1) (G+1) G smoothPartition
          (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>logCellMass G deleted)
          (mixedGiantPrimeTest G f)*average (fun z : MixedPair M=>R (z.1,z.2))‖≤
        9*Real.exp (-Real.exp (giant.target*L)) := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_periodic_mixed_replacement_core
  refine ⟨δ,K,L₀,hδ,hK,hL₀,?_⟩
  intro k₀ c₀
  filter_upwards [hreplace k₀ c₀,eventually_periodic_guard_errors k₀ c₀] with L hcore hguard
  intro G M _ deleted hZ hdeleted hmod hlo hg hb a ha R hR hsum f hf hderiv hA hraw
  have hp := hcore G M deleted hZ hdeleted hmod hlo hg hb a ha R hR hsum f hf hderiv hA hraw
  have hg' := (hguard G M (NeZero.pos M) hmod hlo deleted hdeleted hZ a ha R hR).2 f hraw
  exact (norm_sub_le_norm_sub_add_norm_sub _ (periodicSourceMixedMean G deleted hZ M R f) _).trans
    ((add_le_add hg' hp).trans_eq (by ring))

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
