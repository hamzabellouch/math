import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryRationalFold
import OAI.Combinatorics.KMedian.Binary.BinaryAutomatic

namespace OAI


                                        
section
namespace MetricKMedian.Binary.Automatic.Poly
open PolyProgram
variable {α β γ : Type} [Coding α] [Coding γ]

@[fun_prop] theorem nat_div : Poly (fun x : ℕ × ℕ => x.1/x.2) := ⟨natDiv⟩
@[fun_prop] theorem nat_mod : Poly (fun x : ℕ × ℕ => x.1%x.2) := ⟨natMod⟩
@[fun_prop] theorem nat_pow (n : ℕ) : Poly (fun x : ℕ => x^n) := by
  induction n with
  | zero => simpa only [pow_zero] using const (α:=ℕ) 1
  | succ n ih =>
    simpa only [pow_succ,id_eq] using comp nat_mul (pair ih identity)

 theorem fixed_map (bs : List β) (f : α → β → γ)
    (hf : ∀ b∈bs, Poly (fun x => f x b)) : Poly (fun x => bs.map (f x)) := by
  induction bs with
  | nil => exact const []
  | cons b bs ih =>
    exact comp list_cons (pair (hf b (by simp)) (ih (fun c hc => hf c (by simp [hc]))))

@[fun_prop] theorem rat_prod : Poly (List.prod : List ℚ → ℚ) := ⟨ratProd⟩
@[fun_prop] theorem rat_sum : Poly (List.sum : List ℚ → ℚ) := ⟨ratSum⟩
@[fun_prop] theorem bool_all : Poly (fun xs : List Bool => xs.all id) := ⟨listAll (PolyProgram.identity _) false⟩

end MetricKMedian.Binary.Automatic.Poly
end

end OAI
