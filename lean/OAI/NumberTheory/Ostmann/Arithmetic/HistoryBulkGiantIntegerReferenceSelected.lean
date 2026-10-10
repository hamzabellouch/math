import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReferenceSource
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

theorem selected_corrected_joint_bounds {d : Decomposition} {Bs BD Bz L : ℝ}
    {k₀ : ℕ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀) (hm : 1 ≤ bulkSize k₀ L)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ) (hl : l < k₀)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
    (p q P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
    (hP : 0<P) (hQ : 0<Q) (hPc : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hQc : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1) :
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T (permutedAssignment C l σ x) q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside),
    let eB := integerOrderedEquiv C V l outside σ x p q P Q c e hs
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (eG : κ ≃ giantCoordinates h g),
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k₀ L/2))→ℝ)=>
      jointCorrectedScalar C s h g hs gs eG eB (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
    ∀ z∈logRectangle (fun _ : κ=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (jointCorrectedScalar C s h g hs gs eG eB (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs gs κ _ _ eG
  have hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass
      (permutedAssignment C l σ x) ≠ 0 := by
    rw [permutedAssignment_mass]
    exact hx
  exact reference_corrected_joint_bounds C hBs hk₀ hm s outside houtside hout l hl
    x (permutedAssignment C l σ x) p q P Q c e hx hy hc he hP hQ hPc hQc
    hs gs (integerMatching C (frequencyBound Bs BD Bz k₀ L) l σ x p q P Q c e)
    κ (Fin (2^l)×Fin (2*(bulkSize k₀ L/2))) eG
    (integerOrderedEquiv C (frequencyBound Bs BD Bz k₀ L) l outside σ x p q P Q c e hs)

theorem selected_plain_joint_bounds {d : Decomposition} {Bs BD Bz L : ℝ}
    {k₀ : ℕ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀) (hm : 1 ≤ bulkSize k₀ L)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ) (hl : l ≤ k₀)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
    (p q P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
    (hP : 0<P) (hQ : 0<Q) (hPc : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hQc : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1) :
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T (permutedAssignment C l σ x) q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside),
    let eB := integerOrderedEquiv C V l outside σ x p q P Q c e hs
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (eG : κ ≃ giantCoordinates h g),
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k₀ L/2))→ℝ)=>
      jointScalar C s h g hs gs eG eB (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
    ∀ z∈logRectangle (fun _ : κ=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (jointScalar C s h g hs gs eG eB (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs gs κ _ _ eG
  have hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass
      (permutedAssignment C l σ x) ≠ 0 := by
    rw [permutedAssignment_mass]
    exact hx
  exact reference_plain_joint_bounds C hBs hk₀ hm s outside houtside hout l hl
    x (permutedAssignment C l σ x) p q P Q c e hx hy hc he hP hQ hPc hQc
    hs gs (integerMatching C (frequencyBound Bs BD Bz k₀ L) l σ x p q P Q c e)
    κ (Fin (2^l)×Fin (2*(bulkSize k₀ L/2))) eG
    (integerOrderedEquiv C (frequencyBound Bs BD Bz k₀ L) l outside σ x p q P Q c e hs)

end Ostmann.Arithmetic.HistoryBulkGiantIntegerReference

end

end OAI
