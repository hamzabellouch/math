import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitudeBulk

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude
open Filter Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkCorrectedXiBounds
open HistoryBulkGiantCorrectedBounds PrimeCellFreezing HistorySelectedGiantDensityMass
open HistorySelectedPairDerivativeBounds
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem source_corrected_giantScalar_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k₀ : ℕ} (hBs : 0≤Bs) (hk₀ : 0<k₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ)
    (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (_hblock : Real.exp ((1/20:ℝ)*L) ≤ C.blockBase)
    (_hcenter : C.blockBase-2 < (C.giantCenter:ℝ)) (s : ℕ) {outside : List ℕ}
    (_houtside : ∀ q ∈ outside, 0 < q) (_hout : outside.length = 2*s)
    (l : ℕ) (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (_hl : l < k₀)
    (_hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (_hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (_matchRoots : RootMatching h k)
    (_hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (_hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (eP : Bool ≃ giantCoordinates h k) (eM : Option Unit ≃ giantCoordinates h k)
    (eB : ι ≃ bulkCoordinates h k) (u : ι→C.bulk.Sample),
    ‖primeGiantScalar C.giantCenter (Construction.logCellMass C.giantCenter ∅)
      (jointCorrectedScalar C s h k hs ks eP eB) (fun i=>((u i).val:ℝ))‖ ≤
        64*Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) ∧
    ‖mixedGiantScalar C.giantCenter (Construction.logCellMass C.giantCenter ∅)
      (jointCorrectedScalar C s h k hs ks eM eB) (fun i=>((u i).val:ℝ))‖ ≤
        64*Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  filter_upwards [selected_density_masses_eventually d Bs BD Bz k₀,
    (bulkSize_tendsto_atTop hk₀).eventually_ge_atTop 1] with L hM hm
  intro E C hblock hcenter s outside houtside hout l h k hs ks hl hh hg matchRoots hsrc₁ hsrc₂
    ι _ _ eP eM eB u
  have hm' : 1≤bulkSize k₀ L := by exact_mod_cast hm
  obtain ⟨hG,hZ,hP,hQ⟩ := hM E C hblock hcenter
  constructor
  · apply norm_primeGiantScalar_le hG hZ (Real.exp_nonneg _) hP
    intro z hz
    exact bulkBounds_norm_original_sample C
      (corrected_bulkBounds C hBs hk₀ hm' s houtside hout h k hs ks hl hh hg
        matchRoots hsrc₁ hsrc₂ eP eB z hz) u
  · apply norm_mixedGiantScalar_le hG hZ (Real.exp_nonneg _) hQ
    intro z hz
    exact bulkBounds_norm_original_sample C
      (corrected_bulkBounds C hBs hk₀ hm' s houtside hout h k hs ks hl hh hg
        matchRoots hsrc₁ hsrc₂ eM eB z hz) u

theorem source_plain_giantScalar_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k₀ : ℕ} (hBs : 0≤Bs) (hk₀ : 0<k₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ)
    (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (_hblock : Real.exp ((1/20:ℝ)*L) ≤ C.blockBase)
    (_hcenter : C.blockBase-2 < (C.giantCenter:ℝ)) (s : ℕ) {outside : List ℕ}
    (_houtside : ∀ q ∈ outside, 0 < q) (_hout : outside.length = 2*s)
    (l : ℕ) (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (_hl : l ≤ k₀)
    (_hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (_hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (_matchRoots : RootMatching h k)
    (_hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (_hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (eP : Bool ≃ giantCoordinates h k) (eM : Option Unit ≃ giantCoordinates h k)
    (eB : ι ≃ bulkCoordinates h k) (u : ι→C.bulk.Sample),
    ‖primeGiantScalar C.giantCenter (Construction.logCellMass C.giantCenter ∅)
      (jointScalar C s h k hs ks eP eB) (fun i=>((u i).val:ℝ))‖ ≤
        64*Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) ∧
    ‖mixedGiantScalar C.giantCenter (Construction.logCellMass C.giantCenter ∅)
      (jointScalar C s h k hs ks eM eB) (fun i=>((u i).val:ℝ))‖ ≤
        64*Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  filter_upwards [selected_density_masses_eventually d Bs BD Bz k₀,
    (bulkSize_tendsto_atTop hk₀).eventually_ge_atTop 1] with L hM hm
  intro E C hblock hcenter s outside houtside hout l h k hs ks hl hh hg matchRoots hsrc₁ hsrc₂
    ι _ _ eP eM eB u
  have hm' : 1≤bulkSize k₀ L := by exact_mod_cast hm
  obtain ⟨hG,hZ,hP,hQ⟩ := hM E C hblock hcenter
  constructor
  · apply norm_primeGiantScalar_le hG hZ (Real.exp_nonneg _) hP
    intro z hz
    exact bulkBounds_norm_original_sample C
      (plain_bulkBounds C hBs hk₀ hm' s houtside hout h k hs ks hl hh hg
        matchRoots hsrc₁ hsrc₂ eP eB z hz) u
  · apply norm_mixedGiantScalar_le hG hZ (Real.exp_nonneg _) hQ
    intro z hz
    exact bulkBounds_norm_original_sample C
      (plain_bulkBounds C hBs hk₀ hm' s houtside hout h k hs ks hl hh hg
        matchRoots hsrc₁ hsrc₂ eM eB z hz) u

end Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude

end

end OAI
