import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportPrimeGuarded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportSourceBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators ContDiff
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction Conclusion Filter ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget
open HistoryGiantWeightedPriorReplacement HistoryGiantGridCellBounds HistoryGiantReplacementGeometry
open HistoryGiantReplacementError HistoryPrincipalIntegralAverage HistoryCRTIntegration ResidueHaar
open PrimeCellReplacement PrimeCellFreezing LogCellPartition HistoryGiantPriorGrid
open HistoryPairSmoothXi HistoryOccurrenceVariables HistoryPairPattern HistoryPairBulkCoordinates
open HistoryPairGiantCoordinates HistoryActiveCoordinates HistorySymbolicEncoding HistoryProductWindows
open HistoryBulkGiantCorrectedBounds HistoryBulkReferenceGiantDerivative

theorem plain_prime_source_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0≤Bs) {k₀ : ℕ} (hk₀ : 0<k₀) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀ (l s : ℕ) (outside : List ℕ)
    (_ : ∀ q ∈ outside, 0 < q) (_ : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (_ : l ≤ k₀)
    (_ : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (_ : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (_ : RootMatching h k)
    (_ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (_ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)),
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (eB : ι ≃ bulkCoordinates h k) (u : ι→ℝ), (∀i,0<u i) →
    ∀ (M : ℕ) [NeZero M], Real.log (M:ℝ)≤Real.exp (giant.μ*L) →
    ∀ (deleted : Finset ℕ), deleted.card≤2 → ∀hZ : 0<logCellMass C.giantCenter deleted,
    ∀a : ℕ, a≤residueCostExponent k₀ → ∀R : ZMod M×ZMod M→ℂ,
      (∀z,‖R z‖≤(M:ℝ)^a) → (∑v : Bool→(ZMod M)ˣ,‖primeTest R v‖)≤(M:ℝ)^a →
    ‖guardedPeriodicSourcePrimeMean C.giantCenter deleted hZ M R (fun v => jointScalar C s h k hs ks (boolEquiv h k) eB v u) -
      primeIntegral (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1)
        (fun _=>logCellMass C.giantCenter deleted) (primeCutoff C.giantCenter (fun v => jointScalar C s h k hs ks (boolEquiv h k) eB v u)) * average (fun z : UnitPair M=>R (z.1,z.2))‖≤
      30*Real.exp (-Real.exp (giant.target*L)) := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_guarded_periodic_prime_replacement_core
  filter_upwards [hreplace k₀ (cutoffExponent Bs BD Bz k₀),
    selected_gridCellBounds_eventually d Bs BD Bz hk₀ hK.le hδ L₀,
    (bulkSize_tendsto_atTop hk₀).eventually_ge_atTop (1:ℝ)] with L hrep hgrid hbulk
  intro E C hG hGu hcl hcu hb hd l s outside houtside hout h k hs ks hl hh hk matchRoots
    hsrc₁ hsrc₂ ι _ _ eB u hu M _ hmod deleted hdeleted hZ a ha R hR hsum
  have hm : 1≤bulkSize k₀ L := by exact_mod_cast hbulk
  have hg := hgrid E C hG hGu hcl hcu hb hd M (NeZero.pos M) hmod
  have hcut := plain_prime_giant_bounds C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
    matchRoots hsrc₁ hsrc₂ (boolEquiv h k) eB u hu
  have hraw := plain_giant_bounds C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
    matchRoots hsrc₁ hsrc₂ (boolEquiv h k) eB u hu
  have he := cutoff_exp_le_smoothGrowth Bs BD Bz L k₀
  have her := selected_exp_le_cutoff_smoothGrowth Bs BD Bz L k₀
  apply hrep C.giantCenter M deleted hZ hdeleted hmod hg.1.lower_scale hg.1
    (hg.2 deleted hdeleted).1 a ha R hR hsum (fun v => jointScalar C s h k hs ks (boolEquiv h k) eB v u)
  · intro z hz
    exact hcut.1.differentiable (by simp) z
  · intro z hz i
    exact ((hcut.2 z hz).1 i).trans he
  · intro z hz
    exact ((hcut.2 z hz).2).trans he
  · intro z hz
    exact ((hraw.2 z hz).2).trans her

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
