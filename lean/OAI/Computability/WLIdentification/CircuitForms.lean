import OAI.Computability.WLIdentification.CircuitCodes

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Number
variable {A : Word → Type} (AP : Presented A)

noncomputable def vectorFirst : Number (AP.prod (Presented.bit.prod Presented.bit)) (fun _ x => x.2.1.val) where
  eval _ i := (Nat.unpair (Nat.unpair i).2).1
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair]
  poly := by word_poly
noncomputable def vectorSecond : Number (AP.prod (Presented.bit.prod Presented.bit)) (fun _ x => x.2.2.val) where
  eval _ i := (Nat.unpair (Nat.unpair i).2).2
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair]
  poly := by word_poly

noncomputable def vectorProj {d : ∀ w,A w → ℕ} {j : ∀ w,(a : A w) → Fin (d w a)}
    (J : Number AP (fun w a => (j w a).val)) :
    Number (AP.prod (Presented.bit.prod Presented.bit)) (fun w x => (vectorTwo (d w x.1) x.2 (j w x.1)).val) where
  eval w i := if J.eval w (Nat.unpair i).1=0 then (Nat.unpair (Nat.unpair i).2).1 else (Nat.unpair (Nat.unpair i).2).2
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair,J.correct,vectorTwo]; split <;> rfl
  poly := NatPoly.iteProp (NatPoly.eqtest (J.eval_poly (Poly.var 0) (by word_poly)) (NatPoly.const 0)) (by word_poly) (by word_poly)

theorem sum_vector (d : ℕ) (hd : d=1 ∨ d=2) (a b : Bit) :
    (ProductCircuit.sumForm d (vectorTwo d (a,b))).val = if d=1 then a.val else (a.val+b.val)%2 := by
  rcases hd with rfl|rfl
  · simp [ProductCircuit.sumForm_apply,vectorTwo]
  · simp [ProductCircuit.sumForm_apply,Fin.sum_univ_two,vectorTwo,ZMod.val_add]

noncomputable def vectorSum {d : ∀ w,A w → ℕ} (D : Number AP d) (hd : ∀ w a, d w a=1 ∨ d w a=2) :
    Number (AP.prod (Presented.bit.prod Presented.bit)) (fun w x => (ProductCircuit.sumForm (d w x.1) (vectorTwo _ x.2)).val) where
  eval w i := if D.eval w (Nat.unpair i).1=1 then (Nat.unpair (Nat.unpair i).2).1
    else ((Nat.unpair (Nat.unpair i).2).1+(Nat.unpair (Nat.unpair i).2).2)%2
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair,D.correct,sum_vector _ (hd w x.1)]
  poly := NatPoly.iteProp (NatPoly.eqtest (D.eval_poly (Poly.var 0) (by word_poly)) (NatPoly.const 1)) (by word_poly) (NatPoly.mod (NatPoly.add (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))) (NatPoly.const 2))

noncomputable def vectorAdd : Number (AP.prod (Presented.bit.prod Presented.bit)) (fun _ x => (x.2.1+x.2.2).val) where
  eval _ i := ((Nat.unpair (Nat.unpair i).2).1+(Nat.unpair (Nat.unpair i).2).2)%2
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair,ZMod.val_add]
  poly := NatPoly.mod (NatPoly.add (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))) (NatPoly.const 2)

end Number
namespace CircuitRealizer
variable {P E Z T : Word → Type} {PP : Presented P} {EP : Presented E}
    {ZP : Presented Z} {TP : Presented T} {r : Word → ℕ}
    {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)}
    (F : CircuitRealizer PP EP ZP TP r rp C)

noncomputable def sourceForm : Number (F.connectionP.prod (Presented.bit.prod Presented.bit))
    (fun w x => ((C w).sourceForm x.1 (vectorTwo _ x.2)).val) := by
  apply F.casesNumberFst
  · exact Number.vectorSum EP (F.dimension.comp F.source) (fun w e => (C w).dimension_bound ((C w).source e))
  · exact Number.vectorSum TP (F.dimension.comp F.testType) (fun w t => (C w).dimension_bound ((C w).testType t))
  · exact Number.vectorFirst F.rowP
  · exact Number.vectorFirst F.broadcastP
  · exact Number.vectorProj F.selfP (Number.sigmaSnd F.primaryDim)
  · exact Number.vectorFirst Presented.unit

noncomputable def targetForm : Number (F.connectionP.prod (Presented.bit.prod Presented.bit))
    (fun w x => ((C w).targetForm x.1 (vectorTwo _ x.2)).val) := by
  apply F.casesNumberFst
  · exact Number.vectorProj EP F.port
  · exact Number.vectorFirst TP
  · exact Number.vectorFirst F.rowP
  · exact Number.vectorProj F.broadcastP (Number.sigmaSnd F.dimension)
  · exact Number.vectorProj F.selfP (Number.sigmaSnd F.primaryDim)
  · exact Number.vectorFirst Presented.unit

noncomputable def comparisonLeft : Number (F.comparisonP.prod (Presented.bit.prod Presented.bit))
    (fun w x => ((C w).comparisonLeft x.1 (vectorTwo _ x.2)).val) := by
  apply F.comparisonNumberFst
  · exact Number.vectorSum ZP (F.dimension.comp F.seedType) (fun w z => (C w).dimension_bound ((C w).seedType z))
  · exact F.sourceForm
  · exact F.sourceForm
  · exact Number.vectorAdd F.connectionP

noncomputable def comparisonRight : Number (F.comparisonP.prod (Presented.bit.prod Presented.bit))
    (fun w x => ((C w).comparisonRight x.1 (vectorTwo _ x.2)).val) := by
  apply F.comparisonNumberFst
  · exact Number.const _ 0
  · exact Number.vectorFirst F.connectionP
  · exact Number.vectorSecond F.connectionP
  · exact F.targetForm

noncomputable def schemas : SchemaRealizer F.realP F.comparisonP r rp (fun w => (C w).schemas) where
  pointIndex := F.realIndex
  edgeIndex := F.comparisonIndex
  dimension := F.realDim
  source := F.comparisonSource
  target := F.comparisonTarget
  domain := F.comparisonDomain
  mapping w e i a := F.comparisonMapping.eval w (Nat.pair e (Nat.pair i a))
  mapping_eq w e i a := F.comparisonMapping.correct w (e,i,a.val)
  mapping_poly := F.comparisonMapping.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.var 1) (NatPoly.pair (NatPoly.var 2) (NatPoly.var 3)))
  left := F.comparisonLeft
  right := F.comparisonRight

end CircuitRealizer
end FinitePresentation
end WLIdentification

end OAI
