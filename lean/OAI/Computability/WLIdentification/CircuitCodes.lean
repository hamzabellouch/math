import OAI.Computability.WLIdentification.CircuitPresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Number
variable {A : Word → Type} {P : Presented A}

def sigmaSnd {d : ∀ w,A w → ℕ} (D : Number P d) : Number (P.finSigma D) (fun _ x => x.2.val) where
  eval _ i := (Nat.unpair i).2
  correct w x := by change (Nat.unpair (Nat.pair _ _)).2=_; rw [Nat.unpair_pair]; rfl
  poly := NatPoly.unpair_snd (NatPoly.var 1)

end Number
namespace CircuitRealizer
variable {P E Z T : Word → Type} {PP : Presented P} {EP : Presented E}
    {ZP : Presented Z} {TP : Presented T} {r : Word → ℕ}
    {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)}
    (F : CircuitRealizer PP EP ZP TP r rp C)

noncomputable def primaryIndex : Number F.primaryP (fun w p => NaturalCode.option (C w).pointIndex p) :=
  ((F.pointIndex.add (Number.const PP 1)).optionCases (fun _ => 0) (NatPoly.const 0)).congr (by intro w p; cases p <;> rfl)

noncomputable def connectionIndex : Number F.connectionP (fun w l => (C w).connectionIndex l) := by
  apply F.casesNumber
  · exact (Number.const EP 0).pair F.edgeIndex
  · exact (Number.const TP 1).pair F.testIndex
  · exact (Number.const F.rowP 2).pair (Number.code F.rowP)
  · exact (Number.const F.broadcastP 3).pair ((F.pointIndex.comp (Map.sigmaFst PP F.dimension)).pair (Number.sigmaSnd F.dimension))
  · exact (Number.const F.selfP 4).pair ((F.primaryIndex.comp (Map.sigmaFst F.primaryP F.primaryDim)).pair (Number.sigmaSnd F.primaryDim))
  · exact Number.const Presented.unit (Nat.pair 5 0)

noncomputable def realIndex : Number F.realP (fun w p => (C w).realIndex p) :=
  ((Number.sumCases ((Number.const F.primaryP 0).pair F.primaryIndex)
    (Number.sumCases ((Number.const F.connectionP 1).pair F.connectionIndex) (Number.const Presented.unit (Nat.pair 2 0)))).retype
      (realEquiv (C := C))).congr (by intro w p; cases p <;> rfl)

noncomputable def comparisonIndex : Number F.comparisonP (fun w e => (C w).comparisonIndex e) := by
  apply F.comparisonCases
  · exact (Number.const ZP 0).pair F.seedIndex
  · exact (Number.const F.connectionP 1).pair F.connectionIndex
  · exact (Number.const F.connectionP 2).pair F.connectionIndex
  · exact (Number.const F.connectionP 3).pair F.connectionIndex

noncomputable def realDim : Number F.realP (fun w p => (C w).realDimension p) :=
  ((Number.sumCases F.primaryDim (Number.sumCases (Number.const F.connectionP 2) (Number.const Presented.unit 1))).retype
    (realEquiv (C := C))).congr (by intro w p; cases p <;> rfl)

noncomputable def toPrimary : Map F.primaryP F.realP (fun _ => ProductCircuit.RealType.primary) :=
  (Map.untype F.realBase (realEquiv (C := C))).comp (Map.inl F.primaryP (F.connectionP.sum Presented.unit))
noncomputable def toBuffer : Map F.connectionP F.realP (fun _ => ProductCircuit.RealType.buffer) :=
  (Map.untype F.realBase (realEquiv (C := C))).comp
    ((Map.inr F.primaryP (F.connectionP.sum Presented.unit)).comp (Map.inl F.connectionP Presented.unit))
noncomputable def toDummy {A : Word → Type} (AP : Presented A) : Map AP F.realP (fun _ _ => .dummy) :=
  Map.const AP F.realP (fun _ => .dummy) (NatPoly.const 3)

noncomputable def comparisonSource : Map F.comparisonP F.realP (fun w => (C w).comparisonSource) := by
  apply F.comparisonCases
  · exact F.toPrimary.comp ((Map.some PP).comp F.seedType)
  · exact F.toPrimary.comp F.connectionSource
  · exact F.toPrimary.comp F.connectionSource
  · exact F.toBuffer
noncomputable def comparisonTarget : Map F.comparisonP F.realP (fun w => (C w).comparisonTarget) := by
  apply F.comparisonCases
  · exact F.toDummy ZP
  · exact F.toBuffer
  · exact F.toBuffer
  · exact F.toPrimary.comp F.connectionTarget

noncomputable def connectionDomain : Test (F.connectionP.prod (F.rowP.prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).connectionMap x.1).domain x.2.1)) := by
  apply F.casesTestFst
  · exact F.edgeDomain
  · exact F.testDomain
  all_goals exact (Test.const _ true).congr (by intro w x; simp only [ProductCircuit.connectionMap,ProductMap.flip,ProductMap.identity,Finset.mem_univ,decide_true])

noncomputable def rightBit {A : Word → Type} (AP : Presented A) :
    Map (AP.prod (F.rowP.prod Presented.bool)) Presented.bool (fun _ x => x.2.2) :=
  (Map.snd F.rowP Presented.bool).comp (Map.snd AP (F.rowP.prod Presented.bool))

noncomputable def flipMapping : Map (F.rowP.prod (F.rowP.prod Presented.bool)) Presented.bool
    (fun _w x => (ProductMap.flip x.1).mapping x.2.1 x.2.2) := by
  let H : Test (F.rowP.prod (F.rowP.prod Presented.bool)) (fun _ x => decide (x.2.1=x.1)) :=
    Test.eq ((Map.fst F.rowP Presented.bool).comp (Map.snd F.rowP (F.rowP.prod Presented.bool))) (Map.fst _ _)
  let B := Test.ofBoolMap (F.rightBit F.rowP)
  exact (Map.boolOfTest (Test.ite H B.not B)).congr (by intro w x; simp only [decide_eq_true_eq]; rfl)

noncomputable def connectionMapping : Map (F.connectionP.prod (F.rowP.prod Presented.bool)) Presented.bool
    (fun w x => ((C w).connectionMap x.1).mapping x.2.1 x.2.2) := by
  apply F.casesNumberFst
  · exact F.edgeMapping
  · exact F.rightBit TP
  · exact F.flipMapping
  · exact F.rightBit F.broadcastP
  · exact F.rightBit F.selfP
  · exact F.rightBit Presented.unit

noncomputable def comparisonDomain : Test (F.comparisonP.prod (F.rowP.prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).comparisonMap x.1).domain x.2.1)) := by
  apply F.comparisonTestFst
  · exact F.seedDomain
  · exact F.connectionDomain
  · exact F.connectionDomain
  · exact F.connectionDomain

noncomputable def comparisonMapping : Map (F.comparisonP.prod (F.rowP.prod Presented.bool)) Presented.bool
    (fun w x => ((C w).comparisonMap x.1).mapping x.2.1 x.2.2) := by
  apply F.comparisonNumberFst
  · exact F.rightBit ZP
  · exact F.rightBit F.connectionP
  · exact F.rightBit F.connectionP
  · exact F.connectionMapping

end CircuitRealizer
end FinitePresentation

end WLIdentification

end OAI
