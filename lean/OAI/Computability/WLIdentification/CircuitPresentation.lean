import OAI.Computability.WLIdentification.SchemaPresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

structure CircuitRealizer {P E Z T : Word → Type} (PP : Presented P) (EP : Presented E)
    (ZP : Presented Z) (TP : Presented T) (r : Word → ℕ)
    (rp : NatPoly (fun X : Fin 1 → Word => r (X 0)))
    (C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)) where
  pointIndex : Number PP (fun w p => (C w).pointIndex p)
  edgeIndex : Number EP (fun w e => (C w).edgeIndex e)
  seedIndex : Number ZP (fun w z => (C w).seedIndex z)
  testIndex : Number TP (fun w t => (C w).testIndex t)
  dimension : Number PP (fun w p => (C w).dimension p)
  source : Map EP PP (fun w => (C w).source)
  target : Map EP PP (fun w => (C w).target)
  port : Number EP (fun w e => ((C w).port e).val)
  seedType : Map ZP PP (fun w => (C w).seedType)
  testType : Map TP PP (fun w => (C w).testType)
  edgeDomain : Test (EP.prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).edgeMap x.1).domain x.2.1))
  seedDomain : Test (ZP.prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).seedMap x.1).domain x.2.1))
  testDomain : Test (TP.prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).testMap x.1).domain x.2.1))
  edgeMapping : Map (EP.prod ((Presented.fin r rp).prod Presented.bool)) Presented.bool
    (fun w x => ((C w).edgeMap x.1).mapping x.2.1 x.2.2)

namespace CircuitRealizer
variable {P E Z T : Word → Type} {PP : Presented P} {EP : Presented E}
    {ZP : Presented Z} {TP : Presented T} {r : Word → ℕ}
    {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)}
    (F : CircuitRealizer PP EP ZP TP r rp C)

abbrev rowP (_F : CircuitRealizer PP EP ZP TP r rp C) := Presented.fin r rp
abbrev primaryP (_F : CircuitRealizer PP EP ZP TP r rp C) := PP.option
noncomputable def primaryDim : Number F.primaryP (fun w p => (C w).primaryDimension p) :=
  (F.dimension.optionCases (fun _ => 1) (NatPoly.const 1)).congr (by intro w p; cases p <;> rfl)
abbrev broadcastP := PP.finSigma F.dimension
noncomputable abbrev selfP := F.primaryP.finSigma F.primaryDim
noncomputable abbrev connectionBase := EP.sum (TP.sum (F.rowP.sum (F.broadcastP.sum (F.selfP.sum Presented.unit))))

def connectionEquiv (w : Word) : (C w).Connection ≃ (E w ⊕ (T w ⊕ (Fin (r w) ⊕
    ((Σ p : P w,Fin ((C w).dimension p)) ⊕ ((Σ p : (C w).Primary,Fin ((C w).primaryDimension p)) ⊕ Unit))))) where
  toFun
    | .original e => .inl e
    | .test t => .inr (.inl t)
    | .flip i => .inr (.inr (.inl i))
    | .broadcast p j => .inr (.inr (.inr (.inl ⟨p,j⟩)))
    | .self p j => .inr (.inr (.inr (.inr (.inl ⟨p,j⟩))))
    | .conflict => .inr (.inr (.inr (.inr (.inr ()))))
  invFun
    | .inl e => .original e
    | .inr (.inl t) => .test t
    | .inr (.inr (.inl i)) => .flip i
    | .inr (.inr (.inr (.inl p))) => .broadcast p.1 p.2
    | .inr (.inr (.inr (.inr (.inl p)))) => .self p.1 p.2
    | .inr (.inr (.inr (.inr (.inr _)))) => .conflict
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with e|t|i|p|p|u <;> rfl

noncomputable def connectionP : Presented (fun w => (C w).Connection) := F.connectionBase.retype (connectionEquiv (C := C))

noncomputable def casesNumber {f : ∀ w,(C w).Connection → ℕ}
    (o : Number EP (fun w e => f w (.original e)))
    (t : Number TP (fun w t => f w (.test t)))
    (i : Number F.rowP (fun w i => f w (.flip i)))
    (b : Number F.broadcastP (fun w p => f w (.broadcast p.1 p.2)))
    (s : Number F.selfP (fun w p => f w (.self p.1 p.2)))
    (c : Number Presented.unit (fun w _ => f w .conflict)) : Number F.connectionP f :=
  ((Number.sumCases o (Number.sumCases t (Number.sumCases i (Number.sumCases b (Number.sumCases s c))))).retype
    (connectionEquiv (C := C))).congr (by intro w x; cases x <;> rfl)

noncomputable def casesNumberFst {A : Word → Type} (AP : Presented A) {f : ∀ w,(C w).Connection × A w → ℕ}
    (o : Number (EP.prod AP) (fun w x => f w (.original x.1,x.2)))
    (t : Number (TP.prod AP) (fun w x => f w (.test x.1,x.2)))
    (i : Number (F.rowP.prod AP) (fun w x => f w (.flip x.1,x.2)))
    (b : Number (F.broadcastP.prod AP) (fun w x => f w (.broadcast x.1.1 x.1.2,x.2)))
    (s : Number (F.selfP.prod AP) (fun w x => f w (.self x.1.1 x.1.2,x.2)))
    (c : Number (Presented.unit.prod AP) (fun w x => f w (.conflict,x.2))) : Number (F.connectionP.prod AP) f :=
  ((Number.sumFst o (Number.sumFst t (Number.sumFst i (Number.sumFst b (Number.sumFst s c))))).retypeFst
    (connectionEquiv (C := C))).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

noncomputable def casesTestFst {A : Word → Type} (AP : Presented A) {f : ∀ w,(C w).Connection × A w → Bool}
    (o : Test (EP.prod AP) (fun w x => f w (.original x.1,x.2)))
    (t : Test (TP.prod AP) (fun w x => f w (.test x.1,x.2)))
    (i : Test (F.rowP.prod AP) (fun w x => f w (.flip x.1,x.2)))
    (b : Test (F.broadcastP.prod AP) (fun w x => f w (.broadcast x.1.1 x.1.2,x.2)))
    (s : Test (F.selfP.prod AP) (fun w x => f w (.self x.1.1 x.1.2,x.2)))
    (c : Test (Presented.unit.prod AP) (fun w x => f w (.conflict,x.2))) : Test (F.connectionP.prod AP) f :=
  ((Test.sumFst o (Test.sumFst t (Test.sumFst i (Test.sumFst b (Test.sumFst s c))))).retypeFst
    (connectionEquiv (C := C))).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

noncomputable def connectionSource : Map F.connectionP F.primaryP (fun w => (C w).connectionSource) := by
  apply F.casesNumber
  · exact (Map.some PP).comp F.source
  · exact (Map.some PP).comp F.testType
  · exact Map.none _ _
  · exact Map.none _ _
  · exact Map.sigmaFst _ _
  · exact Map.none _ _
noncomputable def connectionTarget : Map F.connectionP F.primaryP (fun w => (C w).connectionTarget) := by
  apply F.casesNumber
  · exact (Map.some PP).comp F.target
  · exact Map.none _ _
  · exact Map.none _ _
  · exact (Map.some PP).comp (Map.sigmaFst _ _)
  · exact Map.sigmaFst _ _
  · exact Map.none _ _

noncomputable abbrev realBase := F.primaryP.sum (F.connectionP.sum Presented.unit)
def realEquiv (w : Word) : (C w).RealType ≃ ((C w).Primary ⊕ ((C w).Connection ⊕ Unit)) where
  toFun | .primary p => .inl p | .buffer l => .inr (.inl l) | .dummy => .inr (.inr ())
  invFun | .inl p => .primary p | .inr (.inl l) => .buffer l | .inr (.inr _) => .dummy
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with p|l|u <;> rfl
noncomputable def realP : Presented (fun w => (C w).RealType) := F.realBase.retype (realEquiv (C := C))

noncomputable abbrev comparisonBase := ZP.sum (F.connectionP.sum (F.connectionP.sum F.connectionP))
def comparisonEquiv (w : Word) : (C w).Comparison ≃ (Z w ⊕ ((C w).Connection ⊕ ((C w).Connection ⊕ (C w).Connection))) where
  toFun | .seed z => .inl z | .first l => .inr (.inl l) | .second l => .inr (.inr (.inl l)) | .third l => .inr (.inr (.inr l))
  invFun | .inl z => .seed z | .inr (.inl l) => .first l | .inr (.inr (.inl l)) => .second l | .inr (.inr (.inr l)) => .third l
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with z|l|l|l <;> rfl
noncomputable def comparisonP : Presented (fun w => (C w).Comparison) := F.comparisonBase.retype (comparisonEquiv (C := C))

noncomputable def comparisonCases {f : ∀ w,(C w).Comparison → ℕ}
    (z : Number ZP (fun w z => f w (.seed z)))
    (a : Number F.connectionP (fun w l => f w (.first l)))
    (b : Number F.connectionP (fun w l => f w (.second l)))
    (c : Number F.connectionP (fun w l => f w (.third l))) : Number F.comparisonP f :=
  ((Number.sumCases z (Number.sumCases a (Number.sumCases b c))).retype (comparisonEquiv (C := C))).congr
    (by intro w x; cases x <;> rfl)

noncomputable def comparisonNumberFst {A : Word → Type} (AP : Presented A) {f : ∀ w,(C w).Comparison × A w → ℕ}
    (z : Number (ZP.prod AP) (fun w x => f w (.seed x.1,x.2)))
    (a : Number (F.connectionP.prod AP) (fun w x => f w (.first x.1,x.2)))
    (b : Number (F.connectionP.prod AP) (fun w x => f w (.second x.1,x.2)))
    (c : Number (F.connectionP.prod AP) (fun w x => f w (.third x.1,x.2))) : Number (F.comparisonP.prod AP) f :=
  ((Number.sumFst z (Number.sumFst a (Number.sumFst b c))).retypeFst (comparisonEquiv (C := C))).congr
    (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)
noncomputable def comparisonTestFst {A : Word → Type} (AP : Presented A) {f : ∀ w,(C w).Comparison × A w → Bool}
    (z : Test (ZP.prod AP) (fun w x => f w (.seed x.1,x.2)))
    (a : Test (F.connectionP.prod AP) (fun w x => f w (.first x.1,x.2)))
    (b : Test (F.connectionP.prod AP) (fun w x => f w (.second x.1,x.2)))
    (c : Test (F.connectionP.prod AP) (fun w x => f w (.third x.1,x.2))) : Test (F.comparisonP.prod AP) f :=
  ((Test.sumFst z (Test.sumFst a (Test.sumFst b c))).retypeFst (comparisonEquiv (C := C))).congr
    (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

end CircuitRealizer
end FinitePresentation
end WLIdentification

end OAI
