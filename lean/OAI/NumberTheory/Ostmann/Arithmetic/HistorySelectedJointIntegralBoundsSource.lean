import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsMeasure

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

theorem source_integralBounds_eventually (d : Decomposition) (Bs BD Bz : ℝ) (k₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) → IntegralBounds L C.giantCenter E := by
  obtain ⟨L₀,G₀,h⟩ := exists_joint_integral_thresholds
  filter_upwards [eventually_ge_atTop L₀,eventually_ge_atTop (20*(G₀+2))] with L hL hLG
  intro E C hblock hcenter
  have hG : G₀ ≤ (C.giantCenter:ℝ) := by
    have hx := Real.add_one_le_exp ((1/20:ℝ)*L)
    linarith
  intro ι _ _ A hA
  exact h L hL C.giantCenter hG E ∅ C.deleted_card (by simp) ι hA

theorem corrected_integrals_le
    (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hI : IntegralBounds L C.giantCenter E) (s : ℕ) {outside : List ℕ}
    (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (hl : l < k₀)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (matchRoots : RootMatching h k)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (eP : Bool ≃ giantCoordinates h k) (eM : Option Unit ≃ giantCoordinates h k)
    (eB : ι ≃ bulkCoordinates h k) :
    ‖nestedPrimeIntegral L C.giantCenter E
      (jointCorrectedScalar C s h k hs ks eP eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l ∧
    ‖nestedMixedIntegral L C.giantCenter E
      (jointCorrectedScalar C s h k hs ks eM eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l := by
  have hb := hI ι (mainAmplitude Bs k₀ L l) (mainAmplitude_pos Bs k₀ L l).le
  constructor
  · apply hb.1
    intro z hz y hy
    exact jointCorrectedScalar_norm_le C s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eP eB z hz _ (fun i => Real.exp_pos _)
  · apply hb.2
    intro z hz y hy
    exact jointCorrectedScalar_norm_le C s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eM eB z hz _ (fun i => Real.exp_pos _)

theorem plain_integrals_le
    (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hI : IntegralBounds L C.giantCenter E) (s : ℕ) {outside : List ℕ}
    (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (matchRoots : RootMatching h k)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (eP : Bool ≃ giantCoordinates h k) (eM : Option Unit ≃ giantCoordinates h k)
    (eB : ι ≃ bulkCoordinates h k) :
    ‖nestedPrimeIntegral L C.giantCenter E
      (jointScalar C s h k hs ks eP eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l ∧
    ‖nestedMixedIntegral L C.giantCenter E
      (jointScalar C s h k hs ks eM eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l := by
  have hb := hI ι (mainAmplitude Bs k₀ L l) (mainAmplitude_pos Bs k₀ L l).le
  constructor
  · apply hb.1
    intro z hz y hy
    exact jointScalar_norm_le C s houtside hout h k hs ks 
      matchRoots hsrc₁ hsrc₂ eP eB z hz _ (fun i => Real.exp_pos _)
  · apply hb.2
    intro z hz y hy
    exact jointScalar_norm_le C s houtside hout h k hs ks 
      matchRoots hsrc₁ hsrc₂ eM eB z hz _ (fun i => Real.exp_pos _)

end Ostmann.Arithmetic.HistorySelectedJointIntegralBounds

end

end OAI
