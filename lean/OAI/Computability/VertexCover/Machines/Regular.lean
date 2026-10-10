import Mathlib
import OAI.Computability.VertexCover.Machines.PortCode
import OAI.Computability.VertexCover.Machines.RegularRow

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

namespace VertexCover.Machine.TableMachine
open UniqueGames.Foundations.PCP
 theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r=s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt,Prod.eta,Equiv.apply_symm_apply,Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i,hi⟩).1 (GraphTables.relationIndex.symm ⟨i,hi⟩).2
end VertexCover.Machine.TableMachine

namespace VertexCover.Machine.RegularMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables CloudMachine

abbrev degree := internalDegree+1

def flatReverse (H : BaseTable) (x : GraphTables.Table × ℕ) : ℕ :=
  let z := reversePair H (x.1,(x.2/degree,x.2%degree))
  z.2+degree*z.1

def flatRelation (x : GraphTables.Table × ℕ) : GraphTables.RelationTable :=
  relation (x.1,(x.2/degree,x.2%degree))

noncomputable def coordsPoly : Poly (prodBits tableCode natBits) inputCode
    (fun x => (x.1,(x.2/degree,x.2%degree))) := by
  let t := Poly.fst tableCode natBits
  let i := Poly.snd tableCode natBits
  let p := i.pair (Poly.const _ natBits degree)
  exact t.pair ((p.comp Poly.natDiv).pair (p.comp Poly.natMod))

noncomputable def flatReversePoly (H : BaseTable) :
    Poly (prodBits tableCode natBits) natBits (flatReverse H) := by
  let r := coordsPoly.comp (reversePairPoly H)
  let v := r.comp (Poly.fst natBits natBits)
  let p := r.comp (Poly.snd natBits natBits)
  exact (p.pair (((Poly.const _ natBits degree).pair v).comp Poly.natMul)).comp Poly.natAdd

noncomputable def flatRelationPoly : Poly (prodBits tableCode natBits) relationCode flatRelation :=
  coordsPoly.comp relationPoly

 theorem flatReverse_source (H : BaseTable) (T : GraphTables.Table)
    (i : Fin ((vertexCount T (PreprocessingRegularTables.padding T))*degree)) :
    flatReverse H (T,i.val) = (regularize H T).reverseIndex[i].val := by
  let V := vertexOrder T (PreprocessingRegularTables.padding T)
  let P := portOrder internalDegree
  let E := (Equiv.prodCongr V P).trans (PortTables.rowIndex _ degree)
  obtain ⟨⟨e,p⟩,rfl⟩ := E.surjective i
  have hc : ((E (e,p)).val/degree,(E (e,p)).val%degree) = ((V e).val,(P p).val) :=
    congrArg (fun z : Fin (vertexCount T (PreprocessingRegularTables.padding T)) × Fin degree =>
      (z.1.val,z.2.val)) ((PortTables.rowIndex _ degree).symm_apply_apply (V e,P p))
  dsimp only [flatReverse]
  rw [hc,reversePair_source]
  change _ = ((regularize H T).reverseIndex[PortTables.rowIndex _ degree (V e,P p)]).val
  rw [← PortTables.rowIndex_rotation]
  change _ = (PortTables.rowIndex _ degree
    (PortTables.rotation (ofCloudTables T (PreprocessingRegularTables.padding T) (familyCloudTable H T)) (V e,P p))).val
  rw [rotation_ofCloudTables]
  rfl

 theorem flatRelation_source (H : BaseTable) (T : GraphTables.Table)
    (i : Fin ((vertexCount T (PreprocessingRegularTables.padding T))*degree)) :
    flatRelation (T,i.val) = (regularize H T).relations[i] := by
  let V := vertexOrder T (PreprocessingRegularTables.padding T)
  let P := portOrder internalDegree
  let E := (Equiv.prodCongr V P).trans (PortTables.rowIndex _ degree)
  obtain ⟨⟨e,p⟩,rfl⟩ := E.surjective i
  have hc : ((E (e,p)).val/degree,(E (e,p)).val%degree) = ((V e).val,(P p).val) :=
    congrArg (fun z : Fin (vertexCount T (PreprocessingRegularTables.padding T)) × Fin degree =>
      (z.1.val,z.2.val)) ((PortTables.rowIndex _ degree).symm_apply_apply (V e,P p))
  dsimp only [flatRelation]
  rw [hc,relation_source H]
  apply relation_ext
  intro a b
  rw [GraphTables.relationAt_relationOf]
  exact (accepts_ofCloudTables T (PreprocessingRegularTables.padding T) (familyCloudTable H T) e p a b).symm

def regularData (H : BaseTable) (T : GraphTables.Table) : PortMachine.Data :=
  let n := PreprocessingTables.regularVertices T
  (n,((List.range (n*degree)).map (fun i => flatReverse H (T,i)),
      (List.range (n*degree)).map (fun i => flatRelation (T,i))))

 theorem regularData_source (H : BaseTable) (T : GraphTables.Table) :
    regularData H T = PortMachine.erase (regularizeInput H T) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply List.ext_getElem
      · simp [regularData,PortMachine.erase,regularizeInput,PreprocessingTables.regularVertices]
      · intro i h₁ h₂
        simp only [regularData,PortMachine.erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
        exact flatReverse_source H T ⟨i,by simpa [regularData,PreprocessingTables.regularVertices] using h₁⟩
    · apply List.ext_getElem
      · simp [regularData,PortMachine.erase,regularizeInput,PreprocessingTables.regularVertices]
      · intro i h₁ h₂
        simp only [regularData,PortMachine.erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
        exact flatRelation_source H T ⟨i,by simpa [regularData,PreprocessingTables.regularVertices] using h₁⟩

noncomputable def regularLengthPoly : Poly tableCode natBits
    (fun T => PreprocessingTables.regularVertices T*degree) :=
  (regularVerticesPoly.pair (Poly.const tableCode natBits degree)).comp Poly.natMul

noncomputable def reverseListPoly (H : BaseTable) : Poly tableCode (listBits natBits)
    (fun T => (List.range (PreprocessingTables.regularVertices T*degree)).map (fun i => flatReverse H (T,i))) :=
  Poly.tabulate tableCode natBits TableMachine.emptyTable 0 regularLengthPoly (flatReversePoly H)

noncomputable def relationListPoly : Poly tableCode (listBits relationCode)
    (fun T => (List.range (PreprocessingTables.regularVertices T*degree)).map (fun i => flatRelation (T,i))) :=
  Poly.tabulate tableCode relationCode TableMachine.emptyTable relationDefault regularLengthPoly flatRelationPoly

noncomputable def regularDataPoly (H : BaseTable) :
    Poly tableCode PortMachine.dataCode (regularData H) :=
  regularVerticesPoly.pair ((reverseListPoly H).pair relationListPoly)

noncomputable def regularPoly (H : BaseTable) :
    Poly tableCode PortMachine.code (regularizeInput H) := by
  exact (regularDataPoly H).encodeCongr id (fun _ => rfl) (fun T => by
    change PortMachine.dataCode (regularData H T) = PortMachine.dataCode _
    rw [regularData_source])

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
