import Mathlib
import OAI.Computability.QuantumFactoring.NetworkEmissionPack
import OAI.Computability.QuantumFactoring.RawListRange

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def rewireBy (a : Data) (is : List ℕ) : Data:=
  ⟨a.inputs,a.nodes,is.map (fun i=>(a.outputs.drop i).headD 0)⟩
lemma rewireBy_valid (a : Data) (ha : a.Valid) (is : List ℕ) : (rewireBy a is).Valid:=by
  refine ⟨ha.1,?_⟩
  intro i hi
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
  exact headD_drop_bound ha.2 j
lemma rewireBy_mass (a : Data) (is : List ℕ) : (rewireBy a is).mass≤a.mass+is.length:=by
  simp only [rewireBy,Data.mass,Data.width,List.length_map];omega
lemma erase_rewireBy {n m l : ℕ} (a : BooleanNetwork n m) (f : Fin l→Fin m) :
    rewireBy (erase a) (List.ofFn (fun i=>(f i).val))=erase (a.rewire f):=by
  unfold rewireBy erase BooleanNetwork.rewire
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp [(f i).isLt]
def rewirePack (a : Pack) (is : List ℕ) : Pack:=
  ⟨⟨a.val.budget+is.length,rewireBy a.val.value is⟩,rewireBy_valid a.val.value a.property.1 is,
    (rewireBy_mass _ _).trans (Nat.add_le_add_right a.property.2 _)⟩
lemma rewirePack_value {n m l : ℕ} (a : Pack) (b : BooleanNetwork n m) (f : Fin l→Fin m)
    (h : a.val.value=erase b) :
    (rewirePack a (List.ofFn (fun i=>(f i).val))).val.value=erase (b.rewire f):=by
  change rewireBy a.val.value _=_
  rw [h,erase_rewireBy]
def identityPack (n : ℕ) : Pack:=selectPack n (List.range n) (by intro i hi;exact Nat.le_of_lt (List.mem_range.mp hi))
lemma identityPack_value (n : ℕ) : (identityPack n).val.value=erase (BooleanNetwork.select (id : Fin n→Fin n)):=by
  rw [erase_select]
  change select n (List.range n)=select n (List.ofFn (fun i:Fin n=>i.val))
  congr 1
  exact (ofFn_val_range n).symm

def assignPack (n i : ℕ) (v : Pack) : Pack:=
  rewirePack (pairPack (identityPack n) v) ((List.range n).map (fun j=>if j=i then n else j))
lemma assignPack_value {n : ℕ} (i : Fin n) (a : Pack) (v : BooleanNetwork n 1) (ha : a.val.value=erase v) :
    (assignPack n i.val a).val.value=erase (BooleanNetwork.assign i v):=by
  have hp : (pairPack (identityPack n) a).val.value=erase ((BooleanNetwork.select id).pair v):=by
    rw [pairPack_value,identityPack_value,ha,erase_pair]
    rw [identityPack_value,ha];rfl
  have hi : ((List.range n).map (fun j=>if j=i.val then n else j))=
      List.ofFn (fun j:Fin n=>(if j=i then Fin.natAdd n (0 : Fin 1) else j.castAdd 1).val):=by
    rw [←ofFn_val_range,List.map_ofFn]
    congr 1
    funext j
    by_cases h : j=i
    · subst j;simp
    · have hn : j.val≠i.val:=fun hh=>h (Fin.ext hh)
      simp [h,hn]
  rw [assignPack,hi,rewirePack_value _ _ _ hp]
  rfl
namespace Emission
noncomputable def rewireByP : Procedure (prodCode dataCode (listCode Nat.bits)) dataCode
    (fun x=>rewireBy x.1 x.2):=by
  let a:=first dataCode (listCode Nat.bits)
  let is:=second dataCode (listCode Nat.bits)
  let out:=dataOutputsP.comp a
  let get:=(listGet Nat.bits 0).comp ((second (listCode Nat.bits) Nat.bits).pair (first (listCode Nat.bits) Nat.bits))
  let outs:=(listMapWith (f:=fun (xs:List ℕ) i=>(xs.drop i).headD 0) 0 0 get).comp (out.pair is)
  exact (dataPackP.comp ((dataInputP.comp a).pair ((dataNodesP.comp a).pair outs))).congrFun (by intro x;rfl)
noncomputable def rewirePackP : Procedure (prodCode packCode (listCode Nat.bits)) packCode
    (fun x=>rewirePack x.1 x.2):=by
  let a:=first packCode (listCode Nat.bits)
  let is:=second packCode (listCode Nat.bits)
  let v:=rewireByP.comp ((packValueP.comp a).pair is)
  let b:=unaryAdd.comp ((packBudgetP.comp a).pair ((NativeAIG.Emission.listUnaryLength Nat.bits 0).comp is))
  exact (b.pair v).result (by intro x;rfl)
noncomputable def rangeP : Procedure unaryCode (listCode Nat.bits) List.range:=by
  let p:=unaryToBits.comp (first unaryCode emptyCode)
  exact ((tabulate (f:=fun (_:Unit) i=>i) 0 p).comp
    ((identity unaryCode).pair (Procedure.constant _ emptyCode ()))).congrFun (by intro n;exact List.map_id _)
noncomputable def identityPackP : Procedure unaryCode packCode identityPack:=by
  let v:=selectP.comp (unaryToBits.pair rangeP)
  let b:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  exact (b.pair v).result (by intro n;change _=prodCode unaryCode dataCode (n+(List.range n).length,select n (List.range n));rw [List.length_range];rfl)
noncomputable def assignPackP : Procedure (prodCode unaryCode (prodCode Nat.bits packCode)) packCode
    (fun x=>assignPack x.1 x.2.1 x.2.2):=by
  let n:=first unaryCode (prodCode Nat.bits packCode)
  let i:=(first Nat.bits packCode).comp (second unaryCode (prodCode Nat.bits packCode))
  let v:=(second Nat.bits packCode).comp (second unaryCode (prodCode Nat.bits packCode))
  let env:=(unaryToBits.comp n).pair i
  let e:=first (prodCode Nat.bits Nat.bits) Nat.bits
  let j:=second (prodCode Nat.bits Nat.bits) Nat.bits
  let test:=binaryEq.comp (j.pair ((second Nat.bits Nat.bits).comp e))
  let choose:= (conditional test ((first Nat.bits Nat.bits).comp e) j).congrFun
    (show ∀ x : (ℕ×ℕ)×ℕ, _ = (if x.2=x.1.2 then x.1.1 else x.2) from by
      intro x;simp)
  let out:=(listMapWith (f:=fun (e:ℕ×ℕ) j=>if j=e.2 then e.1 else j) 0 0 choose).comp
    (env.pair (rangeP.comp n))
  exact rewirePackP.comp ((pairPackP.comp ((identityPackP.comp n).pair v)).pair out)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
