import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportMixedGuarded
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

theorem corrected_mixed_source_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
    (_houtside : ∀ q ∈ outside, 0 < q) (_hout : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (_hl : l < k₀)
    (_hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (_hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (_matchRoots : RootMatching h k)
    (_hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (_hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)),
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (eB : ι ≃ bulkCoordinates h k) (u : ι→ℝ), (∀i,0<u i) →
    ∀ (M : ℕ) [NeZero M], Real.log (M:ℝ)≤Real.exp (giant.μ*L) →
    ∀ (deleted : Finset ℕ), deleted.card≤2 → ∀hZ : 0<logCellMass C.giantCenter deleted,
    ∀a : ℕ, a≤residueCostExponent k₀ → ∀R : ZMod M×ZMod M→ℂ,
      (∀z,‖R z‖≤(M:ℝ)^a) → (∑r : ZMod M,∑v : Unit→(ZMod M)ˣ,‖mixedTest R r v‖)≤(M:ℝ)^a →
    ‖guardedPeriodicSourceMixedMean C.giantCenter deleted hZ M R (fun v => jointCorrectedScalar C s h k hs ks (optionEquiv h k) eB v u) -
      mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
        (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
        (fun _=>logCellMass C.giantCenter deleted) (mixedGiantPrimeTest C.giantCenter (fun v => jointCorrectedScalar C s h k hs ks (optionEquiv h k) eB v u)) * average (fun z : MixedPair M=>R (z.1,z.2))‖≤
      9*Real.exp (-Real.exp (giant.target*L)) := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_guarded_periodic_mixed_replacement_core
  filter_upwards [hreplace k₀ (cutoffExponent Bs BD Bz k₀),
    selected_gridCellBounds_eventually d Bs BD Bz hk₀ hK.le hδ L₀,
    (bulkSize_tendsto_atTop hk₀).eventually_ge_atTop (1:ℝ)] with L hrep hgrid hbulk
  intro E C hG hGu hcl hcu hb hd l s outside houtside hout h k hs ks hl hh hk matchRoots
    hsrc₁ hsrc₂ ι _ _ eB u hu M _ hmod deleted hdeleted hZ a ha R hR hsum
  have hm : 1≤bulkSize k₀ L := by exact_mod_cast hbulk
  have hg := hgrid E C hG hGu hcl hcu hb hd M (NeZero.pos M) hmod
  have hcut := corrected_mixed_giant_bounds C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
    matchRoots hsrc₁ hsrc₂ (optionEquiv h k) eB u hu
  have hraw := corrected_giant_bounds C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
    matchRoots hsrc₁ hsrc₂ (optionEquiv h k) eB u hu
  have hoc (a : ℝ) : Option.elim' a (fun _ : Unit => a) = (fun _ : Option Unit => a) := by
    funext i
    cases i <;> rfl
  have he := cutoff_exp_le_smoothGrowth Bs BD Bz L k₀
  have her := selected_exp_le_cutoff_smoothGrowth Bs BD Bz L k₀
  apply hrep C.giantCenter M deleted hZ hdeleted hmod hg.1.lower_scale hg.1
    (hg.2 deleted hdeleted).1 a ha R hR hsum (fun v => jointCorrectedScalar C s h k hs ks (optionEquiv h k) eB v u)
  · intro z hz
    exact hcut.1.differentiable (by simp) z
  · intro z hz i
    exact ((hcut.2 z (by simpa only [hoc] using hz)).1 i).trans he
  · intro z hz
    exact ((hcut.2 z (by simpa only [hoc] using hz)).2).trans he
  · intro z hz
    exact ((hraw.2 z (by simpa only [hoc] using hz)).2).trans her

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
