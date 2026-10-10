import Mathlib
import OAI.Computability.VertexCover.Machines.ListFilter
import OAI.Computability.VertexCover.Machines.Generic

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
namespace BinaryOutput
abbrev State := ℕ × List Bool
abbrev enc : State → List Bool := prodBits natBits id
def body (p : State) : Bool × State :=
  if p.1=0 then (false,p) else (true,(p.1/2,decide (p.1%2=1)::p.2))
def result (p : State) : State := (0,p.1.bits.reverse++p.2)
noncomputable def bodyPoly : Poly enc (flagBits enc) body := by
  let n := Poly.fst natBits (id : List Bool → List Bool)
  let bs := Poly.snd natBits (id : List Bool → List Bool)
  let test := n.comp Poly.natZero
  let bit := (((n.pair (Poly.const enc natBits 2)).comp Poly.natMod).pair
    (Poly.const enc natBits 1)).comp Poly.natEq
  let out := bit.ite (bs.comp (Poly.cons true)) (bs.comp (Poly.cons false))
  let next := ((n.pair (Poly.const enc natBits 2)).comp Poly.natDiv).pair out
  exact ((test.comp (Poly.bool Bool.not)).flagPair (test.ite (Poly.identity enc) next)).congr
    (fun p => by
      by_cases h : p.1=0
      · simp [Function.comp_apply,body,h]
      · simp only [Function.comp_apply,body,h,ite_false,decide_false,Bool.not_false]
        congr 2
        by_cases hb : p.1%2=1 <;> simp [hb])
 theorem bits_step (n : ℕ) (hn : n≠0) : n.bits=decide (n%2=1)::(n/2).bits := by
  have he : Nat.bit (decide (n%2=1)) (n/2)=n := by
    have hm := Nat.mod_lt n (by decide : 0<2)
    have hv := Nat.mod_add_div n 2
    by_cases h : n%2=1 <;> simp [Nat.bit,h] <;> omega
  conv_lhs => rw [← he]
  rw [Nat.bits_append_bit _ _ (by
    intro hz
    by_contra hb
    have hh : decide (n%2=1)=false := by cases h : decide (n%2=1) <;> simp_all
    rw [hh,hz] at he
    exact hn he.symm)]
 theorem run (n : ℕ) (xs : List Bool) (B : ℕ) (hsize : (enc (n,xs)).length ≤ B) :
    ∃ k, k≤n+1 ∧ BoundedRun enc body B (n,xs) (result (n,xs)) k := by
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      refine ⟨1,le_rfl,?_⟩
      simpa [body,result] using
        (BoundedRun.stop (e := enc) (body := body) (0,xs) hsize (by simp [body]))
    · have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1<2)
      have hs : (enc (n/2,decide (n%2=1)::xs)).length ≤ B := by
        simp only [enc,prodBits,pairBits_length,natBits_length,id_eq,List.length_cons] at hsize ⊢
        omega
      obtain ⟨k,hk,hr⟩ := ih (n/2) hlt _ hs
      have he : result (n/2,decide (n%2=1)::xs)=result (n,xs) := by
        simp only [result,bits_step n hn,List.reverse_cons,List.append_assoc,List.singleton_append]
      rw [he] at hr
      refine ⟨k+1,by omega,.next _ _ k hsize (by simp [body,hn]) ?_⟩
      simpa only [body,hn,ite_false] using hr
noncomputable def poly : Poly enc enc result :=
  bodyPoly.loop result Polynomial.X (Polynomial.X+1) (by
    intro ⟨n,xs⟩
    obtain ⟨k,hk,hr⟩ := run n xs (enc (n,xs)).length le_rfl
    refine ⟨k,?_,by simpa only [Polynomial.eval_X] using hr⟩
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
      enc,prodBits,pairBits_length,natBits_length,id_eq]
    omega)
end BinaryOutput
noncomputable def Poly.rawReverse : Poly id id (List.reverse : List Bool → List Bool) :=
  ((Poly.rawToList.comp (Poly.listReverse boolBits false)).comp Poly.rawBooleans).congr (fun _ => rfl)
noncomputable def Poly.binaryDigits : Poly natBits id Nat.bits :=
  (((((Poly.identity natBits).pair (Poly.const natBits id ([] : List Bool))).comp BinaryOutput.poly).comp
    (Poly.snd natBits (id : List Bool → List Bool))).comp Poly.rawReverse).congr
      (fun n => by simp only [Function.comp_apply,BinaryOutput.result,List.append_nil,List.reverse_reverse,id_eq])
noncomputable def Poly.binaryFrame : Poly id id UniqueGames.BinaryEncoding.frame := by
  let δ : Unit → Bool → Unit × List Bool := fun _ b => ((),[true,b])
  have h (q : Unit) (bs : List Bool) : Stream.output δ (fun _ => [false]) q bs = UniqueGames.BinaryEncoding.frame bs := by
    induction bs generalizing q with
    | nil => rfl
    | cons b bs ih => simp only [Stream.output,δ,List.cons_append,List.nil_append,ih,UniqueGames.BinaryEncoding.frame]
  exact (Stream.poly () δ (fun _ => [false]) 2 (by simp [δ]) (by simp)).congr (fun bs => h () bs)
noncomputable def Poly.nameBits : Poly natBits id UniqueGames.BinaryEncoding.nameBits :=
  Poly.binaryDigits.comp Poly.binaryFrame
noncomputable def Poly.nameList : Poly (listBits natBits) id
    (fun xs => xs.flatMap UniqueGames.BinaryEncoding.nameBits) :=
  ((Poly.listMap natBits id 0 [] Poly.nameBits).comp Poly.rawFlatten).congr (fun xs => by
    simp only [Function.comp_apply]
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,ih])
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
