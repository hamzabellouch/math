import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualMetadata

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkGiantIntegerReference
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistoryBulkGiantCorrectedBounds HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds
open HistoryGiantReferenceMean HistorySignedXiTransport HistorySelectedPairDerivativeBounds PrimeCellFreezing

theorem reference_corrected_joint_bounds {d : Decomposition} {Bs BD Bz L : ℝ}
    {k₀ : ℕ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀) (hm : 1 ≤ bulkSize k₀ L)
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
    ∀ (κ ι : Type) [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
      (eG : κ ≃ giantCoordinates h g) (eB : ι ≃ bulkCoordinates h g),
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(ι→ℝ)=>
      jointCorrectedScalar C s h g hs gs eG eB (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
    ∀ z∈logRectangle (fun _ : κ=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (jointCorrectedScalar C s h g hs gs eG eB (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs gs hmatch κ ι _ _ _ _ eG eB
  have hsource := selected_reference_sourceBounds C (frequencyBound Bs BD Bz k₀ L) l
    x y p q c e P Q hx hy hc he hP hQ hPc hQc
  have hh := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l x p P Q c
  have hg := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l y q P Q e
  refine ⟨jointCorrectedScalar_log_contDiff C s houtside _ _ hs gs hsource.1 hsource.2 eG eB,?_⟩
  intro z hz
  exact corrected_bulkBounds C hBs hk₀ hm s houtside hout _ _ hs gs hl hh hg
    hmatch hsource.1 hsource.2 eG eB z hz

theorem reference_plain_joint_bounds {d : Decomposition} {Bs BD Bz L : ℝ}
    {k₀ : ℕ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀) (hm : 1 ≤ bulkSize k₀ L)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ) (hl : l ≤ k₀)
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
    ∀ (κ ι : Type) [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
      (eG : κ ≃ giantCoordinates h g) (eB : ι ≃ bulkCoordinates h g),
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(ι→ℝ)=>
      jointScalar C s h g hs gs eG eB (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
    ∀ z∈logRectangle (fun _ : κ=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (jointScalar C s h g hs gs eG eB (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs gs hmatch κ ι _ _ _ _ eG eB
  have hsource := selected_reference_sourceBounds C (frequencyBound Bs BD Bz k₀ L) l
    x y p q c e P Q hx hy hc he hP hQ hPc hQc
  have hh := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l x p P Q c
  have hg := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l y q P Q e
  refine ⟨jointScalar_log_contDiff C s houtside _ _ hs gs hsource.1 hsource.2 eG eB,?_⟩
  intro z hz
  exact plain_bulkBounds C hBs hk₀ hm s houtside hout _ _ hs gs hl hh hg
    hmatch hsource.1 hsource.2 eG eB z hz

end Ostmann.Arithmetic.HistoryBulkGiantIntegerReference

end

end OAI
