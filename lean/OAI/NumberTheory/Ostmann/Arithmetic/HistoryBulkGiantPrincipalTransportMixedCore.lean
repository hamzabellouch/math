import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportSamples
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

theorem exists_periodic_mixed_replacement_core :
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
      ‖periodicSourceMixedMean G deleted hZ M R f-
        mixedIntegral (G-1) (G+1) G smoothPartition
          (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>logCellMass G deleted)
          (mixedGiantPrimeTest G f)*average (fun z : MixedPair M=>R (z.1,z.2))‖≤
        8*Real.exp (-Real.exp (giant.target*L)) := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_periodicSourceMixedMean_replacement_constants
  refine ⟨δ,K,L₀,hδ,hK,hL₀,?_⟩
  intro k₀ c₀
  filter_upwards [eventually_periodic_error_bounds k₀ c₀ hK.le hδ] with L hbudget
  intro G M _ deleted hZ hdeleted hmod hlo hg hb a ha R hR hsum f hf hderiv hA hraw
  let F := smoothGrowthFactor k₀ c₀ giant.μ L
  have hF : 0≤F := Real.exp_nonneg _
  have hQ : 0≤(M:ℝ)^a := by positivity
  have hSm : 0≤∑r : ZMod M,∑u : Unit→(ZMod M)ˣ,‖mixedTest R r u‖ :=
    Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  have hbound := hreplace G deleted hZ M R hg.modulus_lt_cell
    (meshWidth giant L) (fun _=>meshWidth giant L)
    (by have := hg.lower_threshold; linarith) hg.lower_threshold hb.mesh_pos
    (fun _=>⟨hb.mesh_pos,hb.mesh_le_one⟩) hg.modulus_admissible
    (giantPrimeError K δ G deleted) 2 (giantMixedError K δ G L deleted)
    hb.error_nonneg (by norm_num) (giantMixedError_nonneg hb.error_nonneg)
    (fun j i=>(hb.boxes Unit j.2 i).2.2.2.1)
    (fun j i=>(add_le_add le_rfl (hb.boxes Unit j.2 i).2.2.2.1).trans
      (hb.boxes Unit j.2 i).2.2.2.2)
    (fun j=>mixedGridError_le_giantMixedError hb (NeZero.pos M) hg j.1)
    f F (meshWidth giant L) F ((M:ℝ)^a*F) hF hb.mesh_pos.le (mul_nonneg hQ hF)
    le_rfl (fun _=>le_rfl) hf hderiv hA
    (periodic_mixed_sample_bound M R ((M:ℝ)^a) hQ hR G F f hraw)
  have hnum := (hbudget G L₀ M deleted hdeleted hmod hlo hb a ha
    F F ((M:ℝ)^a*F) 0 (∑r : ZMod M,∑u : Unit→(ZMod M)ˣ,‖mixedTest R r u‖)
    hF hF (mul_nonneg hQ hF) le_rfl hSm le_rfl le_rfl le_rfl hQ hsum).2
  have hfinal := hbound.trans hnum
  simp only [mixedTest] at hfinal
  rw [mixedPrincipalIntegral_pair M (G-1) (G+1) G smoothPartition
    (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>logCellMass G deleted)
    (mixedGiantPrimeTest G f) (fun z : MixedPair M=>R (z.1,z.2))] at hfinal
  exact hfinal

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
