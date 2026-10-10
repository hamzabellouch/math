import Mathlib
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

 theorem erase_resize {n m q : ℕ} (h : n=m) (T : ExpanderTables.Table n q) :
    ExpandMachine.erase ⟨m,resizeTable h T⟩ = ExpandMachine.erase ⟨n,T⟩ := by
  subst m
  rfl

def cloudFamily (H : BaseTable) (k : ℕ) : ExpandMachine.Data :=
  if k=0 then (0,[]) else ExpandMachine.erase (ExpandMachine.paddedFamily H k)

noncomputable def cloudFamilyPoly (H : BaseTable) :
    Poly natBits ExpandMachine.dataCode (cloudFamily H) := by
  let c : Poly natBits ExpandMachine.dataCode (fun k => ExpandMachine.erase (ExpandMachine.paddedFamily H k)) :=
    (ExpandMachine.paddedFamilyPoly H).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact Poly.natZero.ite (Poly.const natBits ExpandMachine.dataCode (0,[])) c |>.congr (fun k => by
    simp only [cloudFamily,decide_eq_true_eq])

 theorem cloudFamily_source (H : BaseTable) (T : GraphTables.Table) (v : Fin T.vertices) :
    cloudFamily H (cloud (T,v.val)).length =
      ExpandMachine.erase ⟨cloudSize T v + PreprocessingRegularTables.padding T v,familyCloudTable H T v⟩ := by
  rw [cloud_source,List.length_map]
  change cloudFamily H (cloudSize T v) = _
  by_cases hk : cloudSize T v = 0
  · simp only [cloudFamily,familyCloudTable,hk,↓reduceIte,↓reduceDIte]
    rw [erase_resize]
    simp [ExpandMachine.erase,PreprocessingRegularTables.emptyTable]
  · simp only [cloudFamily,familyCloudTable,hk,↓reduceIte,↓reduceDIte]
    exact (erase_resize _ _).symm

def cloudLookup (H : BaseTable) (p : GraphTables.Table × (ℕ × (ℕ × ℕ))) : ℕ × ℕ :=
  ExpandMachine.lookup internalDegree
    ((cloudFamily H (cloud (p.1,p.2.1)).length).2,p.2.2)

noncomputable def cloudLookupPoly (H : BaseTable) :
    Poly (prodBits tableCode (prodBits natBits pairCode)) pairCode (cloudLookup H) := by
  let t := Poly.fst tableCode (prodBits natBits pairCode)
  let x := Poly.snd tableCode (prodBits natBits pairCode)
  let v := x.comp (Poly.fst natBits pairCode)
  let coords := x.comp (Poly.snd natBits pairCode)
  let rows := ((((t.pair v).comp cloudPoly).comp (Poly.listLength natBits 0)).comp
    (cloudFamilyPoly H)).comp (Poly.snd natBits (listBits natBits))
  exact (rows.pair coords).comp (ExpandMachine.lookupPoly internalDegree)

 theorem cloudLookup_source (H : BaseTable) (T : GraphTables.Table) (v : Fin T.vertices)
    (e : PaddedCloud T (PreprocessingRegularTables.padding T) v) (p : Fin internalDegree) :
    cloudLookup H (T,(v.val,((paddedCloudRank T (PreprocessingRegularTables.padding T) v e).val,p.val))) =
      ((paddedCloudRank T (PreprocessingRegularTables.padding T) v
        ((cloudGraphs T (PreprocessingRegularTables.padding T) (familyCloudTable H T) v).rot (e,p)).1).val,
       ((cloudGraphs T (PreprocessingRegularTables.padding T) (familyCloudTable H T) v).rot (e,p)).2.val) := by
  dsimp only [cloudLookup]
  rw [cloudFamily_source]
  change ExpandMachine.lookup internalDegree
    ((familyCloudTable H T v).rows.toList.map Fin.val,
      ((paddedCloudRank T (PreprocessingRegularTables.padding T) v e).val,p.val)) = _
  rw [ExpandMachine.lookup_erase (familyCloudTable H T v)
    (paddedCloudRank T (PreprocessingRegularTables.padding T) v e,p)]
  simp only [cloudGraphs,GraphTransport.reindex,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.prodCongr_symm,Equiv.symm_symm,Prod.map_apply,Prod.map_fst,Prod.map_snd,Equiv.refl_apply,Equiv.refl_symm,
    paddedCloudRank,Equiv.apply_symm_apply]
  rfl

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
