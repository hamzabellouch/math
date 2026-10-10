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

theorem exists_periodic_prime_replacement_core :
    ∃ δ K L₀ : ℝ, 0<δ ∧ 0<K ∧ 1≤L₀ ∧
    ∀ (k₀ : ℕ) (c₀ : ℝ), ∀ᶠ L : ℝ in atTop,
    ∀ (G : ℝ) (M : ℕ) [NeZero M] (deleted : Finset ℕ) (hZ : 0<logCellMass G deleted),
      deleted.card≤2 → Real.log (M:ℝ)≤Real.exp (giant.μ*L) →
      Real.exp (giant.a₀*L)≤G-1 →
      GeometryBounds δ L₀ G M L → PrimeBounds k₀ δ K L₀ G L M deleted →
    ∀ (a : ℕ), a≤residueCostExponent k₀ →
    ∀ (R : ZMod M×ZMod M→ℂ), (∀z,‖R z‖≤(M:ℝ)^a) →
      (∑u : Bool→(ZMod M)ˣ,‖primeTest R u‖)≤(M:ℝ)^a →
    ∀ (f : (Bool→ℝ)→ℂ),
      (∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
        DifferentiableAt ℝ (fun y=>primeCutoff G f (fun i=>Real.exp (y i))) z) →
      (∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),∀i,
        ‖deriv (fun t=>primeCutoff G f
          (Characters.RationalHistory.Expr.logCurve (fun q=>Real.exp (z q)) i t)) 0‖≤
          smoothGrowthFactor k₀ c₀ giant.μ L) →
      (∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
        ‖primeCutoff G f (fun i=>Real.exp (z i))‖≤ smoothGrowthFactor k₀ c₀ giant.μ L) →
      (∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
        ‖f (fun i=>Real.exp (z i))‖≤ smoothGrowthFactor k₀ c₀ giant.μ L) →
      ‖periodicSourcePrimeMean G deleted hZ M R f-
        primeIntegral (fun _ : Bool=>G-1) (fun _=>G+1) (fun _=>logCellMass G deleted)
          (primeCutoff G f)*average (fun z : UnitPair M=>R (z.1,z.2))‖≤
        29*Real.exp (-Real.exp (giant.target*L)) := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_periodicSourcePrimeMean_replacement_constants
  refine ⟨δ,K,L₀,hδ,hK,hL₀,?_⟩
  intro k₀ c₀
  filter_upwards [eventually_periodic_error_bounds k₀ c₀ hK.le hδ] with L hbudget
  intro G M _ deleted hZ hdeleted hmod hlo hg hb a ha R hR hsum f hf hderiv hA hraw
  let F := smoothGrowthFactor k₀ c₀ giant.μ L
  have hF : 0≤F := Real.exp_nonneg _
  have hQ : 0≤(M:ℝ)^a := by positivity
  have hSp : 0≤∑u : Bool→(ZMod M)ˣ,‖primeTest R u‖ := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have hbound := hreplace G deleted hZ M R hg.modulus_lt_cell (fun _=>meshWidth giant L)
    hg.lower_threshold (fun _=>⟨hb.mesh_pos,hb.mesh_le_one⟩) hg.modulus_admissible
    (giantPrimeError K δ G deleted) 2 hb.error_nonneg (by norm_num)
    (fun j i=>(hb.boxes Bool j i).2.2.2.1)
    (fun j i=>(add_le_add le_rfl (hb.boxes Bool j i).2.2.2.1).trans
      (hb.boxes Bool j i).2.2.2.2)
    f F (meshWidth giant L) F ((M:ℝ)^a*F) hF hb.mesh_pos.le (mul_nonneg hQ hF)
    (fun _=>le_rfl) hf hderiv hA
    (periodic_prime_sample_bound M R ((M:ℝ)^a) hQ hR G F f hraw)
  have hnum := (hbudget G L₀ M deleted hdeleted hmod hlo hb a ha
    F F ((M:ℝ)^a*F) (∑u : Bool→(ZMod M)ˣ,‖primeTest R u‖) 0
    hF hF (mul_nonneg hQ hF) hSp le_rfl le_rfl le_rfl le_rfl hsum hQ).1
  have he (ε : ℝ) : 2*ε*(2:ℝ)^2=8*ε := by ring
  have hfinal := hbound.trans (by simpa only [he] using hnum)
  simp only [primeTest] at hfinal
  rw [principalIntegral_pair M (fun _ : Bool=>G-1) (fun _=>G+1)
    (fun _=>logCellMass G deleted) (primeCutoff G f)
    (fun z : UnitPair M=>R (z.1,z.2))] at hfinal
  exact hfinal

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
