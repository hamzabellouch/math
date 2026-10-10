import Mathlib
import OAI.Computability.VertexCover.Machines.Naturals

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
namespace Divide
abbrev State := ℕ × (ℕ × ℕ)
abbrev enc : State → List Bool := prodBits natBits (prodBits natBits natBits)

def body (p : State) : Bool × State :=
  if 0 < p.1 ∧ p.1 ≤ p.2.1 then (true,(p.1,(p.2.1-p.1,p.2.2+1))) else (false,p)

def result (p : State) : State := (p.1,(p.2.1%p.1,p.2.2+p.2.1/p.1))

noncomputable def bodyPoly : Poly enc (flagBits enc) body := by
  let d := Poly.fst natBits (prodBits natBits natBits)
  let rq := Poly.snd natBits (prodBits natBits natBits)
  let r := rq.comp (Poly.fst natBits natBits)
  let q := rq.comp (Poly.snd natBits natBits)
  let test := ((d.comp Poly.natPositive).pair ((d.pair r).comp Poly.natLE)).comp
    (Poly.bool₂ (fun p => p.1 && p.2))
  let next := d.pair (((r.pair d).comp Poly.natSub).pair (q.comp Poly.natSucc))
  exact (test.flagPair (test.ite next (Poly.identity enc))).congr (by
    intro ⟨d,r,q⟩
    simp only [Function.comp_apply,body]
    by_cases hd : 0<d <;> by_cases hr : d ≤ r <;> simp [hd,hr])

theorem run (d r q B : ℕ) (hsize : (enc (d,(r,q))).length ≤ B) :
    ∃ n, n ≤ r+1 ∧ BoundedRun enc body B (d,(r,q)) (result (d,(r,q))) n := by
  induction r using Nat.strong_induction_on generalizing q with
  | h r ih =>
    by_cases h : 0<d ∧ d ≤ r
    · have hlt : r-d < r := Nat.sub_lt (h.1.trans_le h.2) h.1
      have hs : (enc (d,(r-d,q+1))).length ≤ B := by
        simp only [enc,prodBits,pairBits_length,natBits_length] at hsize ⊢
        omega
      obtain ⟨n,hn,hr⟩ := ih (r-d) hlt (q+1) hs
      refine ⟨n+1,by omega,?_⟩
      have he : result (d,(r-d,q+1)) = result (d,(r,q)) := by
        simp only [result]
        rw [Nat.mod_eq_sub_mod h.2,Nat.div_eq_sub_div h.1 h.2]
        congr 2; omega
      rw [he] at hr
      refine .next _ _ n hsize ?_ ?_
      · simp [body,h]
      · simpa [body,h] using hr
    · have he : result (d,(r,q)) = (d,(r,q)) := by
        by_cases hd : d=0
        · simp [result,hd]
        · have hlt : r<d := by omega
          simp [result,Nat.mod_eq_of_lt hlt,Nat.div_eq_of_lt hlt]
      rw [he]
      refine ⟨1,by omega,?_⟩
      simpa only [body,h,ite_false] using
        (BoundedRun.stop (e := enc) (body := body) (d,(r,q)) hsize
          (by simp [body,h]))

noncomputable def poly : Poly enc enc result :=
  bodyPoly.loop result Polynomial.X (Polynomial.X+1) (by
    intro ⟨d,r,q⟩
    obtain ⟨n,hn,hr⟩ := run d r q (enc (d,(r,q))).length le_rfl
    refine ⟨n,?_,by simpa only [Polynomial.eval_X] using hr⟩
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,enc,prodBits,
      pairBits_length,natBits_length]
    omega)
end Divide

noncomputable def Poly.natDivMod : Poly (prodBits natBits natBits) (prodBits natBits natBits)
    (fun p : ℕ × ℕ => (p.1%p.2,p.1/p.2)) := by
  let input := (Poly.snd natBits natBits).pair
    ((Poly.fst natBits natBits).pair (Poly.const (prodBits natBits natBits) natBits 0))
  exact ((input.comp Divide.poly).comp (Poly.snd natBits (prodBits natBits natBits))).congr
    (fun p => by simp only [Function.comp_apply,Divide.result,Nat.zero_add])

noncomputable def Poly.natDiv : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1/p.2) := Poly.natDivMod.comp (Poly.snd natBits natBits)

noncomputable def Poly.natMod : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1%p.2) := Poly.natDivMod.comp (Poly.fst natBits natBits)

noncomputable def Poly.natPow (k : ℕ) : Poly natBits natBits (fun n => n^k) := by
  induction k with
  | zero => exact (Poly.const natBits natBits 1).congr (fun _ => rfl)
  | succ k ih =>
    exact ((ih.pair (Poly.identity natBits)).comp Poly.natMul).congr
      (fun n => (Nat.pow_succ n k).symm)

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
