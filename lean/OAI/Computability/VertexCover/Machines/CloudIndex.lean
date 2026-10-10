import Mathlib
import OAI.Computability.VertexCover.Machines.ListIndex
import OAI.Computability.VertexCover.Machines.Cloud

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

namespace VertexCover.Machine.CloudMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables

 theorem idxOf_map_injective {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.idxOf_cons]
    have h : (f x == f a) = (x == a) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,hf.eq_iff]
    rw [h,ih]

 theorem getD_idxOf {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a d : α) (h : a ∈ xs) : xs.getD (xs.idxOf a) d = a := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_idxOf h]
  rfl

abbrev Dummy (T : GraphTables.Table) := Σ v : Fin T.vertices, Fin (PreprocessingRegularTables.padding T v)
def dummyErase {T : GraphTables.Table} (z : Dummy T) : ℕ × ℕ := (z.1.val,z.2.val)
 theorem dummyErase_injective (T : GraphTables.Table) : Function.Injective (dummyErase (T := T)) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  have hv : v=w := Fin.ext (congrArg Prod.fst h)
  subst w
  have hi : i=j := Fin.ext (congrArg Prod.snd h)
  subst j
  rfl

 theorem dummies_idx (T : GraphTables.Table) (z : Dummy T) :
    (dummies T).idxOf (dummyErase z) = (paddingOrder (PreprocessingRegularTables.padding T) z).val := by
  rw [dummies_source]
  exact idxOf_map_injective dummyErase (dummyErase_injective T) _ z

 theorem dummies_get (T : GraphTables.Table) (z : Dummy T) :
    (dummies T).getD (paddingOrder (PreprocessingRegularTables.padding T) z).val (0,0) = dummyErase z := by
  rw [← dummies_idx]
  apply getD_idxOf
  rw [dummies_source]
  exact List.mem_map.mpr ⟨z,mem_paddingList _ z,rfl⟩

 theorem cloud_idx (T : GraphTables.Table) (v : Fin T.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics T) v) :
    (cloud (T,v.val)).idxOf e.val.val = (cloudRank T v e).val := by
  rw [cloud_source]
  exact idxOf_map_injective Fin.val Fin.val_injective _ _

 theorem cloud_get (T : GraphTables.Table) (v : Fin T.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics T) v) :
    (cloud (T,v.val)).getD (cloudRank T v e).val 0 = e.val.val := by
  rw [← cloud_idx]
  apply getD_idxOf
  rw [cloud_source]
  exact List.mem_map.mpr ⟨e.val,(mem_cloudDarts T v _).mpr e.property,rfl⟩

def ownerRank (p : GraphTables.Table × ℕ) : ℕ × ℕ :=
  if p.2 < p.1.darts then
    let v := ((tableData p.1).2.getD p.2 rowDefault).1.1
    (v,(cloud (p.1,v)).idxOf p.2)
  else
    let z := (dummies p.1).getD (p.2-p.1.darts) (0,0)
    (z.1,(cloud (p.1,z.1)).length+z.2)

noncomputable def ownerRankPoly : Poly (prodBits tableCode natBits) pairCode ownerRank := by
  let e := prodBits tableCode natBits
  let t := Poly.fst tableCode natBits
  let i := Poly.snd tableCode natBits
  let m := t.comp dartsPoly
  let v := tailPoly
  let old := v.pair ((i.pair ((t.pair v).comp cloudPoly)).comp
    (Poly.listIdxOf natBits 0 Poly.natEq))
  let z := (((i.pair m).comp Poly.natSub).pair (t.comp dummiesPoly)).comp
    (Poly.listGetD pairCode (0,0))
  let zv := z.comp (Poly.fst natBits natBits)
  let zj := z.comp (Poly.snd natBits natBits)
  let len := ((t.pair zv).comp cloudPoly).comp (Poly.listLength natBits 0)
  let new := zv.pair ((len.pair zj).comp Poly.natAdd)
  exact ((i.pair m).comp Poly.natLt).ite old new |>.congr (fun p => by
    simp only [ownerRank,Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,
      List.getD_eq_getElem?_getD,decide_eq_true_eq])

def globalIndex (p : GraphTables.Table × (ℕ × ℕ)) : ℕ :=
  let xs := cloud (p.1,p.2.1)
  if p.2.2 < xs.length then xs.getD p.2.2 0
  else p.1.darts + (dummies p.1).idxOf (p.2.1,p.2.2-xs.length)

noncomputable def globalIndexPoly : Poly (prodBits tableCode pairCode) natBits globalIndex := by
  let t := Poly.fst tableCode pairCode
  let x := Poly.snd tableCode pairCode
  let v := x.comp (Poly.fst natBits natBits)
  let i := x.comp (Poly.snd natBits natBits)
  let xs := (t.pair v).comp cloudPoly
  let len := xs.comp (Poly.listLength natBits 0)
  let old := (i.pair xs).comp (Poly.listGetD natBits 0)
  let index := (v.pair ((i.pair len).comp Poly.natSub)).pair (t.comp dummiesPoly)
  let new := ((t.comp dartsPoly).pair (index.comp
    (Poly.listIdxOf pairCode (0,0) Poly.natPairEq))).comp Poly.natAdd
  exact ((i.pair len).comp Poly.natLt).ite old new |>.congr (fun p => by
    simp only [globalIndex,Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,
      List.getD_eq_getElem?_getD,decide_eq_true_eq])

 theorem ownerRank_source (T : GraphTables.Table)
    (e : Vertex T (PreprocessingRegularTables.padding T)) :
    ownerRank (T,(vertexOrder T (PreprocessingRegularTables.padding T) e).val) =
      ((DegreeReplacement.paddedGraph (GraphTables.semantics T)
          (fun v => Fin (PreprocessingRegularTables.padding T v))).tail e |>.val,
       (paddedCloudRank T (PreprocessingRegularTables.padding T) _ ⟨e,rfl⟩).val) := by
  cases e with
  | inl e =>
    rw [vertexOrder_original]
    rw [ownerRank,ite_eq_left e.isLt,lookup_valid]
    change (_,_) = (T.rows[e].tail.val,(cloudRank T T.rows[e].tail ⟨e,rfl⟩).val)
    exact Prod.ext rfl (cloud_idx T T.rows[e].tail ⟨e,rfl⟩)
  | inr z =>
    rw [vertexOrder_dummy]
    dsimp only [ownerRank]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left,dummies_get]
    simp only [dummyErase,cloud_source,List.length_map]
    rfl

 theorem globalIndex_source (T : GraphTables.Table) (v : Fin T.vertices)
    (e : PaddedCloud T (PreprocessingRegularTables.padding T) v) :
    globalIndex (T,(v.val,(paddedCloudRank T (PreprocessingRegularTables.padding T) v e).val)) =
      (vertexOrder T (PreprocessingRegularTables.padding T) e.val).val := by
  rcases e with ⟨e,h⟩
  cases e with
  | inl e =>
    have he : (GraphTables.semantics T).tail e = v := h
    change globalIndex (T,(v.val,(cloudRank T v ⟨e,he⟩).val)) = e.val
    dsimp only [globalIndex]
    rw [ite_eq_left (by simpa only [cloud_source,List.length_map,cloudSize] using (cloudRank T v ⟨e,he⟩).isLt)]
    exact cloud_get T v ⟨e,he⟩
  | inr z =>
    have hz : z.1 = v := h
    rcases z with ⟨w,j⟩
    dsimp only at hz
    subst w
    change globalIndex (T,(v.val,cloudSize T v+j.val)) = _
    dsimp only [globalIndex]
    rw [show (cloud (T,v.val)).length = cloudSize T v by simp [cloud_source,cloudSize]]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    exact congrArg (T.darts+·) (dummies_idx T ⟨v,j⟩)

end VertexCover.Machine.CloudMachine
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
