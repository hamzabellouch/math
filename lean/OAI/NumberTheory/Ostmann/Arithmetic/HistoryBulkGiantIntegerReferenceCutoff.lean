import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReferenceSelected
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

theorem selected_corrected_prime_joint_bounds {d : Decomposition} {Bs BD Bz L : ℝ}
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
    let eG := boolEquiv h g
    ContDiff ℝ ∞ (fun z : (Bool→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k₀ L/2))→ℝ)=>
      primeJointCutoff C.giantCenter (jointCorrectedScalar C s h g hs gs eG eB) (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
    ∀ z∈logRectangle (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (primeJointCutoff C.giantCenter (jointCorrectedScalar C s h g hs gs eG eB) (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs gs
  exact primeJointCutoff_joint_bounds C.giantCenter _
    (selected_corrected_joint_bounds C hBs hk₀ hm s outside houtside hout l hl σ x p q P Q c e
      hx hc he hP hQ hPc hQc hs gs (Bool) (boolEquiv _ _))

theorem selected_corrected_mixed_joint_bounds {d : Decomposition} {Bs BD Bz L : ℝ}
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
    let eG := optionEquiv h g
    ContDiff ℝ ∞ (fun z : (Option Unit→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k₀ L/2))→ℝ)=>
      mixedJointCutoff C.giantCenter (jointCorrectedScalar C s h g hs gs eG eB) (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
    ∀ z∈logRectangle (fun _ : Option Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (mixedJointCutoff C.giantCenter (jointCorrectedScalar C s h g hs gs eG eB) (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs gs
  exact mixedJointCutoff_joint_bounds C.giantCenter _
    (selected_corrected_joint_bounds C hBs hk₀ hm s outside houtside hout l hl σ x p q P Q c e
      hx hc he hP hQ hPc hQc hs gs (Option Unit) (optionEquiv _ _))

theorem selected_plain_prime_joint_bounds {d : Decomposition} {Bs BD Bz L : ℝ}
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
    let eG := boolEquiv h g
    ContDiff ℝ ∞ (fun z : (Bool→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k₀ L/2))→ℝ)=>
      primeJointCutoff C.giantCenter (jointScalar C s h g hs gs eG eB) (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
    ∀ z∈logRectangle (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (primeJointCutoff C.giantCenter (jointScalar C s h g hs gs eG eB) (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs gs
  exact primeJointCutoff_joint_bounds C.giantCenter _
    (selected_plain_joint_bounds C hBs hk₀ hm s outside houtside hout l hl σ x p q P Q c e
      hx hc he hP hQ hPc hQc hs gs (Bool) (boolEquiv _ _))

theorem selected_plain_mixed_joint_bounds {d : Decomposition} {Bs BD Bz L : ℝ}
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
    let eG := optionEquiv h g
    ContDiff ℝ ∞ (fun z : (Option Unit→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k₀ L/2))→ℝ)=>
      mixedJointCutoff C.giantCenter (jointScalar C s h g hs gs eG eB) (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
    ∀ z∈logRectangle (fun _ : Option Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (mixedJointCutoff C.giantCenter (jointScalar C s h g hs gs eG eB) (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs gs
  exact mixedJointCutoff_joint_bounds C.giantCenter _
    (selected_plain_joint_bounds C hBs hk₀ hm s outside houtside hout l hl σ x p q P Q c e
      hx hc he hP hQ hPc hQc hs gs (Option Unit) (optionEquiv _ _))

end Ostmann.Arithmetic.HistoryBulkGiantIntegerReference

end

end OAI
