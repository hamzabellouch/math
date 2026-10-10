import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListMap

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α β γ : Type}
 theorem pushMapWith (f : γ × α → β) (as : List α) (c : γ) (bs : List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) (c,bs)=(c,(as.map (fun a => f (c,a))).reverse++bs) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.foldl_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using ih (f (c,a)::bs)
 theorem pushMapWith_pair (f : γ × α → β) (as : List α) (x : γ × List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) x=(x.1,(as.map (fun a => f (x.1,a))).reverse++x.2) := by
  cases x
  exact pushMapWith _ _ _ _
 theorem filterMapPair (p : γ × α → Bool) (c : γ) (as : List α) :
    (((as.map (fun a => (c,a))).filter p).map Prod.snd)=as.filter (fun a => p (c,a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons,List.filter_cons]
      split <;> simp_all only [List.map_cons]
end ListAlgorithms

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def listMapWith {f : γ × α → β}
    (P : PolyProgram (encodePair ec ea) eb f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.map (fun a => f (x.1,a))) := by
  let eacc := encodePair ec (encodeList eb)
  let acc := fst eacc ea
  let c := acc.comp (fst ec (encodeList eb))
  let bs := acc.comp (snd ec (encodeList eb))
  let a := snd eacc ea
  let nb := ((c.fanout a).comp P).fanout bs
  let step : PolyProgram (encodePair eacc ea) eacc (fun x : (γ × List β) × α => (x.1.1,f (x.1.1,x.2)::x.1.2)) :=
    (c.fanout (nb.comp (listCons eb))).congr _ (fun _ => rfl)
  let B : Polynomial ℕ := 3*X+X*(2*P.sizeBound.comp (3*X+1)+1)+1
  let fold := step.listFold a0 B (by
    intro as x pre suf he
    let L := (encodePair (encodeList ea) eacc (as,x)).length
    have hc : (ec x.1).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hb : (encodeList eb x.2).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hp : (encodeList ea pre).length ≤ L := by
      have hh : (encodeList ea pre).length ≤ (encodeList ea as).length := by rw [he,EncodedList.append,List.length_append]; omega
      simp only [L,encodePair_length]; omega
    have hplen : pre.length ≤ L := (EncodedList.length_le ea pre).trans hp
    have hout := EncodedList.length_bound eb (pre.map (fun a => f (x.1,a))) (P.sizeBound.eval (3*L+1)) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound (x.1,a)).trans
      apply polynomial_eval_mono
      have hla := (EncodedList.member_length ea pre a ha).trans hp
      simp only [encodePair_length]
      omega)
    rw [List.length_map] at hout
    simp only [ListAlgorithms.pushMapWith_pair,eacc,encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
    simp only [B,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
    simp only [L,eacc,encodePair_length] at hc hb hplen hout
    nlinarith)
  let start := (snd ec (encodeList ea)).fanout ((fst ec (encodeList ea)).fanout (constant (encodePair ec (encodeList ea)) (encodeList eb) []))
  exact (((start.comp fold).comp (snd ec (encodeList eb))).comp (listReverse eb b0)).congr _ (fun x => by
    simp only [Function.comp_apply,ListAlgorithms.pushMapWith,List.append_nil,List.reverse_reverse])

noncomputable def listFilterWith {p : γ × α → Bool}
    (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) (c0 : γ) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList ea) (fun x => x.2.filter (fun a => p (x.1,a))) := by
  let attach := (identity (encodePair ec ea)).listMapWith a0 (c0,a0)
  let filt := listFilter P (c0,a0)
  let drop := (snd ec ea).listMap (c0,a0)
  exact ((attach.comp filt).comp drop).congr _ (fun x => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.filterMapPair])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
