import OAI.Computability.WLIdentification.CarryPresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CellularRealizer
open CellularCircuit
variable (A : Type) [Fintype A] (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0)))
noncomputable abbrev pointP := Presented.fixed (Gate A)
noncomputable abbrev tripleP := Presented.fixed (A × A × A)
abbrev digitP := Presented.fin d dp
abbrev kindP := ((digitP d dp).prod (digitP d dp).option).sum ((digitP d dp).sum
  (((digitP d dp).prod (digitP d dp).option).sum (Presented.unit.sum Presented.unit)))
noncomputable abbrev edgeBase := (kindP d dp).prod (tripleP A)
def edgeEquiv (w : Word) : Connection (d w) A ≃
    (((Fin (d w) × Option (Fin (d w))) ⊕ (Fin (d w) ⊕ ((Fin (d w) × Option (Fin (d w))) ⊕ (Unit ⊕ Unit)))) × (A × A × A)) :=
  Connection.equiv.trans (Equiv.prodComm _ _)
noncomputable def edgeP : Presented (fun w => Connection (d w) A) := (edgeBase A d dp).retype (edgeEquiv A d)

noncomputable def casesNumber {f : ∀ w,Connection (d w) A → ℕ}
    (l : Number (((digitP d dp).prod (digitP d dp).option).prod (tripleP A))
      (fun w x => f w (.left x.2.1 x.2.2.1 x.2.2.2 x.1.1 x.1.2)))
    (c : Number ((digitP d dp).prod (tripleP A))
      (fun w x => f w (.center x.2.1 x.2.2.1 x.2.2.2 x.1)))
    (r : Number (((digitP d dp).prod (digitP d dp).option).prod (tripleP A))
      (fun w x => f w (.right x.2.1 x.2.2.1 x.2.2.2 x.1.1 x.1.2)))
    (j : Number (Presented.unit.prod (tripleP A))
      (fun w x => f w (.join x.2.1 x.2.2.1 x.2.2.2)))
    (o : Number (Presented.unit.prod (tripleP A))
      (fun w x => f w (.output x.2.1 x.2.2.1 x.2.2.2))) : Number (edgeP A d dp) f :=
  ((Number.sumFst l (Number.sumFst c (Number.sumFst r (Number.sumFst j o)))).retype (edgeEquiv A d)).congr
    (by intro w x; cases x <;> rfl)

noncomputable def pointIndex : Number (pointP A) (fun _ p => gateIndex p) := Number.fixed _ gateIndex
noncomputable def dimension : Number (pointP A) (fun _ p => dimension p) := Number.fixed (Gate A) CellularCircuit.dimension

noncomputable def edgeIndex : Number (edgeP A d dp) (fun _ e => connectionIndex e) :=
  ((Number.pair ((Number.fixed (A × A × A) (fun a => Nat.pair (NaturalCode.fixed A a.1)
    (Nat.pair (NaturalCode.fixed A a.2.1) (NaturalCode.fixed A a.2.2)))).comp (Map.snd _ _))
    (Number.code (kindP d dp) |>.comp (Map.fst _ _))).retype (edgeEquiv A d)).congr
    (by intro w x; cases x <;> rfl)

noncomputable def source : Map (edgeP A d dp) (pointP A) (fun _ => CellularCircuit.source) := by
  apply casesNumber
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.scalar a.1))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.scalar a.2.1))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.scalar a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.first a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.second a.1 a.2.1 a.2.2))).comp (Map.snd _ _)

noncomputable def target (F : A → A → A → A) : Map (edgeP A d dp) (pointP A) (fun _ => CellularCircuit.target F) := by
  apply casesNumber
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.first a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.first a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.second a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.second a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.scalar (F a.1 a.2.1 a.2.2)))).comp (Map.snd _ _)

noncomputable def port (F : A → A → A → A) : Number (edgeP A d dp) (fun _ e => (CellularCircuit.port F e).val) := by
  apply casesNumber
  · exact Number.const _ 0
  · exact Number.const _ 1
  · exact Number.const _ 1
  · exact Number.const _ 0
  · exact Number.const _ 0

noncomputable def edgeMap : ProductRealizer (edgeP A d dp) (fun w => d w+d w) (NatPoly.add dp dp)
    (fun _ => CellularCircuit.edgeMap) := by
  let C := ProductRealizer.carry d dp
  let R := ProductRealizer.cycle d dp
  let I := ProductRealizer.identity (digitP d dp) d dp
  let L := (C.comp (Map.fst _ _)).concat (R.comp (Map.snd _ _))
  let H := C.concat I
  let B := (C.comp (Map.fst _ _)).concat (R.inverse.comp (Map.snd _ _))
  let J := ProductRealizer.identity Presented.unit (fun w => d w+d w) (NatPoly.add dp dp)
  exact (((L.sumCases (H.sumCases (B.sumCases (J.sumCases J)))).comp (Map.fst _ _)).comp
    (Map.retype (edgeBase A d dp) (edgeEquiv A d))).congr (by intro w x; cases x <;> rfl)

end CellularRealizer
end FinitePresentation
end WLIdentification

end OAI
