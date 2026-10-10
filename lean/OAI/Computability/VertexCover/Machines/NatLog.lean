import Mathlib
import OAI.Computability.VertexCover.Machines.NatDiv

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
namespace Logarithm
abbrev State := ℕ × ℕ
abbrev enc : State → List Bool := prodBits natBits natBits

def body (p : State) : Bool × State :=
  if 2 ≤ p.1 then (true,(p.1/2,p.2+1)) else (false,p)
def result (p : State) : State := (min p.1 1,p.2+p.1.log2)
noncomputable def bodyPoly : Poly enc (flagBits enc) body := by
  let n := Poly.fst natBits natBits
  let c := Poly.snd natBits natBits
  let test := ((Poly.const enc natBits 2).pair n).comp Poly.natLE
  let next := ((n.pair (Poly.const enc natBits 2)).comp Poly.natDiv).pair (c.comp Poly.natSucc)
  exact (test.flagPair (test.ite next (Poly.identity enc))).congr (fun p => by
    by_cases h : 2 ≤ p.1 <;> simp [Function.comp_apply,body,h])
 theorem run (n c B : ℕ) (hsize : (enc (n,c)).length ≤ B) :
    ∃ k, k ≤ n+1 ∧ BoundedRun enc body B (n,c) (result (n,c)) k := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases h : 2 ≤ n
    · have hlt := Nat.div_lt_self (by omega : 0<n) (by decide : 1<2)
      have hs : (enc (n/2,c+1)).length ≤ B := by
        simp only [enc,prodBits,pairBits_length,natBits_length] at hsize ⊢
        omega
      obtain ⟨k,hk,hr⟩ := ih (n/2) hlt (c+1) hs
      have he : result (n/2,c+1) = result (n,c) := by
        simp only [result]
        rw [Nat.log2_def n,ite_eq_left h]
        apply Prod.ext <;> simp only
        · omega
        · omega
      rw [he] at hr
      refine ⟨k+1,by omega,.next _ _ k hsize (by simp [body,h]) ?_⟩
      simpa only [body,h,ite_true] using hr
    · have he : result (n,c) = (n,c) := by
        simp only [result,Nat.log2_def n,ite_eq_right h,Nat.add_zero]
        congr 1
        omega
      rw [he]
      refine ⟨1,by omega,?_⟩
      simpa only [body,h,ite_false] using (BoundedRun.stop (e := enc) (body := body) (n,c) hsize (by simp [body,h]))
noncomputable def poly : Poly enc enc result :=
  bodyPoly.loop result Polynomial.X (Polynomial.X+1) (by
    intro ⟨n,c⟩
    obtain ⟨k,hk,hr⟩ := run n c (enc (n,c)).length le_rfl
    refine ⟨k,?_,by simpa only [Polynomial.eval_X] using hr⟩
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,enc,prodBits,pairBits_length,natBits_length]
    omega)
end Logarithm
noncomputable def Poly.natLog2 : Poly natBits natBits Nat.log2 :=
  ((((Poly.identity natBits).pair (Poly.const natBits natBits 0)).comp Logarithm.poly).comp
    (Poly.snd natBits natBits)).congr (fun n => by simp only [Function.comp_apply,Logarithm.result,Nat.zero_add,id_eq])
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
