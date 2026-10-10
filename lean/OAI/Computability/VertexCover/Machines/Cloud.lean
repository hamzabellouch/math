import Mathlib
import OAI.Computability.VertexCover.Machines.ExpanderFamily
import OAI.Computability.VertexCover.Machines.ListFilter

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

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace TableMachine

def emptyTable : GraphTables.Table := GraphTables.ofGraph (n := 0)
  { reverse := Equiv.refl (Fin 0),reverse_involutive := fun _ => rfl,
    tail := fun e => e.elim0,accepts := fun _ _ _ => true,reverse_accepts := fun _ _ _ => rfl }

end TableMachine

namespace CloudMachine
open TableMachine

abbrev pairCode := prodBits natBits natBits

def cloud (p : GraphTables.Table × ℕ) : List ℕ :=
  (List.range p.1.darts).filter (fun i => ((tableData p.1).2.getD i rowDefault).1.1 == p.2)

noncomputable def cloudPoly : Poly (prodBits tableCode natBits) (listBits natBits) cloud := by
  let ea := prodBits tableCode natBits
  let ctx := Poly.fst ea natBits
  let t := ctx.comp (Poly.fst tableCode natBits)
  let v := ctx.comp (Poly.snd tableCode natBits)
  let i := Poly.snd ea natBits
  let test := (((t.pair i).comp tailPoly).pair v).comp Poly.natEq
  let len := (Poly.fst tableCode natBits).comp dartsPoly
  exact (((Poly.identity ea).pair (len.comp Poly.range)).comp
    (Poly.listFilterWith ea natBits (emptyTable,0) 0 test))

def padding (p : GraphTables.Table × ℕ) : ℕ :=
  let k := (cloud p).length
  PreprocessingLevels.cloudPaddedSize k-k

noncomputable def paddingPoly : Poly (prodBits tableCode natBits) natBits padding := by
  let k := cloudPoly.comp (Poly.listLength natBits 0)
  exact ((k.comp ExpandMachine.cloudPaddedPoly).pair k).comp Poly.natSub

def localDummies (p : GraphTables.Table × ℕ) : List (ℕ × ℕ) :=
  (List.range (padding p)).map (p.2,·)

noncomputable def localDummiesPoly : Poly (prodBits tableCode natBits) (listBits pairCode) localDummies :=
  (((Poly.snd tableCode natBits).pair (paddingPoly.comp Poly.range)).comp
    (Poly.withParam natBits natBits 0 0))

def dummies (T : GraphTables.Table) : List (ℕ × ℕ) :=
  (List.range T.vertices).flatMap (fun v => localDummies (T,v))

noncomputable def dummiesPoly : Poly tableCode (listBits pairCode) dummies :=
  ((Poly.tabulate tableCode (listBits pairCode) emptyTable [] verticesPoly localDummiesPoly).comp
    (Poly.listFlatten pairCode (0,0))).congr (fun T => by
      rfl)

 theorem map_finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

 theorem cloud_source (T : GraphTables.Table) (v : Fin T.vertices) :
    cloud (T,v.val) = (PreprocessingCloudIndex.cloudDarts T v).map Fin.val := by
  unfold cloud PreprocessingCloudIndex.cloudDarts
  rw [← map_finRange_val]
  rw [List.filter_map]
  apply congrArg (List.map Fin.val)
  congr 1
  funext e
  change (((tableData T).2.getD e.val rowDefault).1.1 == v.val) = _
  rw [lookup_valid]
  simp only [rowData,Fin.ext_iff]
  rfl

 theorem padding_source (T : GraphTables.Table) (v : Fin T.vertices) :
    padding (T,v.val) = PreprocessingRegularTables.padding T v := by
  simp only [padding,cloud_source,List.length_map,PreprocessingRegularTables.padding,
    PreprocessingCloudIndex.cloudSize]

 theorem dummies_source (T : GraphTables.Table) :
    dummies T = (PreprocessingRegularTables.paddingList (PreprocessingRegularTables.padding T)).map
      (fun z => (z.1.val,z.2.val)) := by
  unfold dummies PreprocessingRegularTables.paddingList
  rw [← map_finRange_val,List.flatMap_map]
  simp only [List.sigma,List.map_flatMap,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro v _
  simp only [localDummies,padding_source]
  rw [← map_finRange_val,List.map_map]
  rfl

noncomputable def regularVerticesPoly : Poly tableCode natBits PreprocessingTables.regularVertices := by
  let c := (dartsPoly.pair (dummiesPoly.comp (Poly.listLength pairCode (0,0)))).comp Poly.natAdd
  exact c.congr (fun T => by
    simp only [Function.comp_apply,dummies_source,List.length_map,
      PreprocessingRegularTables.paddingList_length,PreprocessingTables.regularVertices,
      PreprocessingRegularTables.vertexCount])

end CloudMachine
end VertexCover.Machine
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
