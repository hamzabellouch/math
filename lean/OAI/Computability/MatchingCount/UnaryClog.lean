import OAI.Computability.MatchingCount.RawOptimizerCompiler

namespace OAI

section

namespace BinaryMatching.StackCode

def unaryClog (x : ℕ) : ℕ :=
  ((List.range (x+1)).find? (fun j => decide (x≤cappedPow2 x j))).getD 0

lemma unaryClog_eq (x : ℕ) : unaryClog x=Nat.clog 2 x := by
  have hk : Nat.clog 2 x≤x := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hp (j : ℕ) : (x≤cappedPow2 x j) ↔ Nat.clog 2 x≤j := by
    rw [cappedPow2_eq,le_min_iff]
    simpa only [le_refl,true_and] using (Nat.clog_le_iff_le_pow (by decide : 1<2) (x := x) (y := j)).symm
  have hf : (List.range (x+1)).find? (fun j => decide (x≤cappedPow2 x j))=some (Nat.clog 2 x) := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simp [hp],Nat.clog 2 x,by simpa using Nat.lt_succ_of_le hk,by simp,?_⟩
    intro j hj
    simp only [List.getElem_range,Bool.not_eq_true',decide_eq_false_iff_not,hp]
    omega
  simp only [unaryClog,hf,Option.getD_some]

namespace Poly
@[fun_prop] theorem natClog2 : Poly (Nat.clog 2) := by
  have hf := Poly.findWith (fun x : ℕ => List.range (x+1))
    (fun z : ℕ×ℕ => decide (z.1≤cappedPow2 z.1 z.2)) (by fun_prop) (by fun_prop)
  have h : Poly unaryClog := by unfold unaryClog; fun_prop
  exact h.congr unaryClog_eq

@[fun_prop] theorem powClog2 : Poly (fun x : ℕ => 2^(Nat.clog 2 x)) := by
  have hbound (x : ℕ) : 2^(Nat.clog 2 x)≤2*x+1 := by
    by_cases hx : x≤1
    · rw [Nat.clog_of_right_le_one hx]; simp
    · have hpos : 0<Nat.clog 2 x := Nat.clog_pos (by decide) (by omega)
      have hh : 2^(Nat.clog 2 x-1)<x := by
        simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<x)
      have he : 2^(Nat.clog 2 x)=2^(Nat.clog 2 x-1)*2 := by rw [←pow_succ,Nat.sub_add_cancel hpos]
      rw [he]
      omega
  have h : Poly (fun x : ℕ => cappedPow2 (2*x+1) (Nat.clog 2 x)) := by fun_prop
  exact h.congr (fun x => cappedPow2_of_le _ _ (hbound x))
end Poly
end BinaryMatching.StackCode
end

end OAI
