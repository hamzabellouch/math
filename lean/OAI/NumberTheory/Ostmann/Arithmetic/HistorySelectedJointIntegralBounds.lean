import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedJointIntegralBounds
open Filter Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkCorrectedXiBounds
open HistoryBulkGiantCorrectedBounds PrimeCellFreezing
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem selected_corrected_integrals_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (k₀ : ℕ) :
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
    (eB : ι ≃ bulkCoordinates h k),
    ‖nestedPrimeIntegral L C.giantCenter E
      (jointCorrectedScalar C s h k hs ks eP eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l ∧
    ‖nestedMixedIntegral L C.giantCenter E
      (jointCorrectedScalar C s h k hs ks eM eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l := by
  filter_upwards [source_integralBounds_eventually d Bs BD Bz k₀] with L hI
  intro E C hblock hcenter s outside houtside hout l h k hs ks hl hh hk  matchRoots hsrc₁ hsrc₂
    ι _ _ eP eM eB
  exact corrected_integrals_le C (hI E C hblock hcenter) s houtside hout h k hs ks hl hh hk 
    matchRoots hsrc₁ hsrc₂ eP eM eB

theorem selected_plain_integrals_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (k₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ)
    (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (_hblock : Real.exp ((1/20:ℝ)*L) ≤ C.blockBase)
    (_hcenter : C.blockBase-2 < (C.giantCenter:ℝ)) (s : ℕ) {outside : List ℕ}
    (_houtside : ∀ q ∈ outside, 0 < q) (_hout : outside.length = 2*s)
    (l : ℕ) (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (_matchRoots : RootMatching h k)
    (_hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (_hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (eP : Bool ≃ giantCoordinates h k) (eM : Option Unit ≃ giantCoordinates h k)
    (eB : ι ≃ bulkCoordinates h k),
    ‖nestedPrimeIntegral L C.giantCenter E
      (jointScalar C s h k hs ks eP eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l ∧
    ‖nestedMixedIntegral L C.giantCenter E
      (jointScalar C s h k hs ks eM eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l := by
  filter_upwards [source_integralBounds_eventually d Bs BD Bz k₀] with L hI
  intro E C hblock hcenter s outside houtside hout l h k hs ks  matchRoots hsrc₁ hsrc₂
    ι _ _ eP eM eB
  exact plain_integrals_le C (hI E C hblock hcenter) s houtside hout h k hs ks 
    matchRoots hsrc₁ hsrc₂ eP eM eB

end Ostmann.Arithmetic.HistorySelectedJointIntegralBounds

end

end OAI
