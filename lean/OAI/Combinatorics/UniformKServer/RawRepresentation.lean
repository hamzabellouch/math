import Mathlib
import OAI.Combinatorics.UniformKServer.LinearProgram
import OAI.Combinatorics.UniformKServer.RawTyped
import OAI.Combinatorics.UniformKServer.FiniteRepresentation

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.RawRepresentation
open RawArithmetic RawWords RawTable RawTyped

theorem requests_injective {n : ℕ} : Function.Injective (@requests n) :=
  List.map_injective_iff.mpr Fin.val_injective

theorem config_injective {n k : ℕ} : Function.Injective (@config n k) := by
  intro c c' hh
  funext j
  apply Fin.ext
  have he:=congrArg (fun xs : List ℕ=>xs.getD j.val 0) hh
  simpa only [config_get] using he

theorem lift_list {n : ℕ} (w : List ℕ) (hw : ∀x∈w,x<n) :
    ∃v : List (Fin n),requests v=w := by
  refine ⟨w.attach.map (fun x=>⟨x.val,hw x.val x.property⟩),?_⟩
  simp [requests,List.map_map]

theorem lift_config {n k : ℕ} (c : List ℕ) (hc : c∈words n k) :
    ∃v : Configuration n k,config v=c := by
  obtain ⟨hlen,hmem⟩:= (mem_words n k c).mp hc
  let v : Configuration n k := fun j=>
    ⟨c.get ⟨j.val,by omega⟩,hmem _ (List.getElem_mem (by omega))⟩
  refine ⟨v,?_⟩
  apply List.ext_getElem
  · simp [config,hlen]
  · intro i hi hi'
    simp only [config,List.getElem_ofFn,v,List.get_eq_getElem]

abbrev Index (n k H : ℕ) := EffectiveLP.Word n H × Configuration n k × Fin n × Fin k

def indexKey {n k H : ℕ} (i : Index n k H) :=
  key (requests i.1.val) (config i.2.1) i.2.2.1.val i.2.2.2.val

theorem index_inj {n k H : ℕ} : Function.Injective (@indexKey n k H) := by
  intro a b hab
  have he:=Encodable.encode_injective (α:=List ℕ×List ℕ×ℕ×ℕ) hab
  have hp : a.1=b.1 := Subtype.ext (requests_injective (congrArg Prod.fst he))
  have hc : a.2.1=b.2.1 := config_injective (congrArg (fun z=>z.2.1) he)
  have hr : a.2.2.1=b.2.2.1 := Fin.ext (congrArg (fun z=>z.2.2.1) he)
  have hj : a.2.2.2=b.2.2.2 := Fin.ext (congrArg (fun z=>z.2.2.2) he)
  exact Prod.ext hp (Prod.ext hc (Prod.ext hr hj))

theorem represents {n k : ℕ} (H : ℕ)
    (N : (List (Fin n)×Configuration n k)→Fin n→Fin k→ℕ) :
    ∃ T : List ℕ,∀p c r j,p.length≤H→
      entry T (requests p) (config c) r.val j.val=N (p,c) r j := by
  obtain ⟨T,hT⟩:=FiniteRepresentation.represents (@indexKey n k H) index_inj
    (fun i : Index n k H=>N (i.1.val,i.2.1) i.2.2.1 i.2.2.2) 0
  refine ⟨T,?_⟩
  intro p c r j hp
  exact hT (⟨p,(EffectiveLP.mem_words p).mpr hp⟩,c,r,j)

end UniformKServer.RawRepresentation

end


end

end OAI
