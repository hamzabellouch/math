import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReferenceSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedJointIntegralBounds
open Filter Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistoryBulkGiantCorrectedBounds HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds
open HistoryGiantReferenceMean HistorySignedXiTransport HistoryBulkGiantIntegerReference PrimeCellFreezing

theorem reference_corrected_integrals_le {d : Decomposition} {Bs BD Bz L : ℝ}
    {k₀ : ℕ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hI : IntegralBounds L C.giantCenter E)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ) (hl : l < k₀)
    (x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
    (p q P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x ≠ 0)
    (hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass y ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
    (hP : 0<P) (hQ : 0<Q) (hPc : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hQc : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1) :
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside), RootMatching h g →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (eB : ι ≃ bulkCoordinates h g),
    ‖nestedPrimeIntegral L C.giantCenter E
      (jointCorrectedScalar C s h g hs gs (boolEquiv h g) eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l ∧
    ‖nestedMixedIntegral L C.giantCenter E
      (jointCorrectedScalar C s h g hs gs (optionEquiv h g) eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l := by
  dsimp only
  intro hs gs hmatch ι _ _ eB
  have hsource := selected_reference_sourceBounds C (frequencyBound Bs BD Bz k₀ L) l
    x y p q c e P Q hx hy hc he hP hQ hPc hQc
  have hh := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l x p P Q c
  have hg := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l y q P Q e
  exact corrected_integrals_le C hI s houtside hout _ _ hs gs hl hh hg
    hmatch hsource.1 hsource.2 (boolEquiv _ _) (optionEquiv _ _) eB

theorem reference_plain_integrals_le {d : Decomposition} {Bs BD Bz L : ℝ}
    {k₀ : ℕ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hI : IntegralBounds L C.giantCenter E)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ)
    (x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
    (p q P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x ≠ 0)
    (hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass y ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
    (hP : 0<P) (hQ : 0<Q) (hPc : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hQc : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1) :
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside), RootMatching h g →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (eB : ι ≃ bulkCoordinates h g),
    ‖nestedPrimeIntegral L C.giantCenter E
      (jointScalar C s h g hs gs (boolEquiv h g) eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l ∧
    ‖nestedMixedIntegral L C.giantCenter E
      (jointScalar C s h g hs gs (optionEquiv h g) eB)‖ ≤
        64*2^Fintype.card ι*mainAmplitude Bs k₀ L l := by
  dsimp only
  intro hs gs hmatch ι _ _ eB
  have hsource := selected_reference_sourceBounds C (frequencyBound Bs BD Bz k₀ L) l
    x y p q c e P Q hx hy hc he hP hQ hPc hQc
  exact plain_integrals_le C hI s houtside hout _ _ hs gs 
    hmatch hsource.1 hsource.2 (boolEquiv _ _) (optionEquiv _ _) eB

end Ostmann.Arithmetic.HistorySelectedJointIntegralBounds

end

end OAI
