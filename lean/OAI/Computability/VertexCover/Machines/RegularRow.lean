import Mathlib
import OAI.Computability.VertexCover.Machines.CloudIndex
import OAI.Computability.VertexCover.Machines.CloudFamily

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                      
section

namespace VertexCover.Machine.RegularMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables CloudMachine

abbrev inputCode := prodBits tableCode pairCode

def reversePair (H : BaseTable) (x : GraphTables.Table × (ℕ × ℕ)) : ℕ × ℕ :=
  if x.2.2 < internalDegree then
    let w := ownerRank (x.1,x.2.1)
    let z := cloudLookup H (x.1,(w.1,(w.2,x.2.2)))
    (globalIndex (x.1,(w.1,z.1)),z.2)
  else
    (if x.2.1 < x.1.darts then ((tableData x.1).2.getD x.2.1 rowDefault).1.2 else x.2.1,
      internalDegree)

noncomputable def reversePairPoly (H : BaseTable) : Poly inputCode pairCode (reversePair H) := by
  let e := inputCode
  let t := Poly.fst tableCode pairCode
  let x := Poly.snd tableCode pairCode
  let v := x.comp (Poly.fst natBits natBits)
  let p := x.comp (Poly.snd natBits natBits)
  let c := Poly.const e natBits internalDegree
  let w := (t.pair v).comp ownerRankPoly
  let wv := w.comp (Poly.fst natBits natBits)
  let wi := w.comp (Poly.snd natBits natBits)
  let z := (t.pair (wv.pair (wi.pair p))).comp (cloudLookupPoly H)
  let newV := (t.pair (wv.pair (z.comp (Poly.fst natBits natBits)))).comp globalIndexPoly
  let inner := newV.pair (z.comp (Poly.snd natBits natBits))
  let rev := (t.pair v).comp TableMachine.reversePoly
  let inherited := (((v.pair (t.comp dartsPoly)).comp Poly.natLt).ite rev v).pair c
  exact ((p.pair c).comp Poly.natLt).ite inner inherited |>.congr (fun x => by
    simp only [reversePair,Function.comp_apply,decide_eq_true_eq])

def equalityRelation : GraphTables.RelationTable := GraphTables.relationOf (fun a b => decide (a=b))
def trueRelation : GraphTables.RelationTable := GraphTables.relationOf (fun _ _ => true)

def relation (x : GraphTables.Table × (ℕ × ℕ)) : GraphTables.RelationTable :=
  if x.2.2 < internalDegree then equalityRelation
  else if x.2.1 < x.1.darts then ((tableData x.1).2.getD x.2.1 rowDefault).2
  else trueRelation

noncomputable def relationPoly : Poly inputCode relationCode relation := by
  let t := Poly.fst tableCode pairCode
  let x := Poly.snd tableCode pairCode
  let v := x.comp (Poly.fst natBits natBits)
  let p := x.comp (Poly.snd natBits natBits)
  let old := (t.pair v).comp TableMachine.relationPoly
  let inherited := ((v.pair (t.comp dartsPoly)).comp Poly.natLt).ite old
    (Poly.const _ relationCode trueRelation)
  exact ((p.pair (Poly.const _ natBits internalDegree)).comp Poly.natLt).ite
    (Poly.const _ relationCode equalityRelation) inherited |>.congr (fun x => by
      simp only [relation,Function.comp_apply,decide_eq_true_eq])

 theorem reversePair_source (H : BaseTable) (T : GraphTables.Table)
    (e : Vertex T (PreprocessingRegularTables.padding T)) (p : Fin internalDegree ⊕ Unit) :
    reversePair H (T,((vertexOrder T (PreprocessingRegularTables.padding T) e).val,
      (portOrder internalDegree p).val)) =
    ((vertexOrder T (PreprocessingRegularTables.padding T)
      ((sourcePortGraph T (PreprocessingRegularTables.padding T) (familyCloudTable H T)).rot (e,p)).1).val,
     (portOrder internalDegree
      ((sourcePortGraph T (PreprocessingRegularTables.padding T) (familyCloudTable H T)).rot (e,p)).2).val) := by
  cases p with
  | inl p =>
    dsimp only [reversePair]
    rw [portOrder_internal,ite_eq_left p.isLt,ownerRank_source,cloudLookup_source]
    rw [globalIndex_source]
    rfl
  | inr u =>
    cases u
    dsimp only [reversePair]
    rw [portOrder_inherited,ite_eq_right (Nat.lt_irrefl _)]
    cases e with
    | inl e =>
      rw [vertexOrder_original,ite_eq_left e.isLt,lookup_valid]
      rfl
    | inr z =>
      rw [vertexOrder_dummy,ite_eq_right (by omega)]
      rfl

 theorem relation_source (H : BaseTable) (T : GraphTables.Table)
    (e : Vertex T (PreprocessingRegularTables.padding T)) (p : Fin internalDegree ⊕ Unit) :
    relation (T,((vertexOrder T (PreprocessingRegularTables.padding T) e).val,
      (portOrder internalDegree p).val)) =
      GraphTables.relationOf (fun a b =>
        (sourceGraph T (PreprocessingRegularTables.padding T) (familyCloudTable H T)).accepts (e,p) a b) := by
  cases p with
  | inl p =>
    dsimp only [relation]
    rw [portOrder_internal,ite_eq_left p.isLt]
    rfl
  | inr u =>
    cases u
    dsimp only [relation]
    rw [portOrder_inherited,ite_eq_right (Nat.lt_irrefl _)]
    cases e with
    | inl e =>
      rw [vertexOrder_original,ite_eq_left e.isLt,lookup_valid]
      change T.rows[e].relation = GraphTables.relationOf _
      apply Vector.ext
      intro i hi
      change T.rows[e].relation[i] = (GraphTables.relationOf
        (GraphTables.relationAt T.rows[e].relation))[i]
      simp only [GraphTables.relationOf,Vector.getElem_ofFn,GraphTables.relationAt,
        Prod.eta,Equiv.apply_symm_apply,Fin.getElem_fin]
    | inr z =>
      rw [vertexOrder_dummy,ite_eq_right (by omega)]
      rfl

end VertexCover.Machine.RegularMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
