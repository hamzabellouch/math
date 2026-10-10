import OAI.Computability.MatchingCount.RawContraction

namespace OAI

section

namespace BinaryMatching.Raw.Compiler
open StackCode StackCode.Poly
@[fun_prop] theorem doubleNatSum {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℕ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => (tab (n a) (fun i => (tab (n a) (fun j => f ((a,i),j))).sum)).sum) := by
  apply Poly.comp List.sum _ Poly.listNatSum
  apply Poly.rawTab n (fun z : α×ℕ => (tab (n z.1) (fun j => f (z,j))).sum) hn
  apply Poly.comp List.sum _ Poly.listNatSum
  exact Poly.rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf

@[fun_prop] theorem outside_poly : Poly (fun z : ℕ×Cut => outside z.1 z.2) := by
  unfold outside
  exact Poly.findWith (fun z : ℕ×Cut => List.range z.1)
    (fun z : (ℕ×Cut)×ℕ => !mem z.1.2 z.2) (by fun_prop) (by fun_prop)
@[fun_prop] theorem contractMap_poly : Poly (fun z : Cut×(ℕ×ℕ) => contractMap z.1 z.2.1 z.2.2) := by
  unfold contractMap
  fun_prop
@[fun_prop] theorem contract_poly : Poly (fun z : ℕ×(Matrix ℕ×(Cut×ℕ)) => contract z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold contract
  apply Poly.rawMatrix Prod.fst
    (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => if z.1.2=z.2 then 0 else
      (tab z.1.1.1 (fun u => (tab z.1.1.1 (fun v =>
        if contractMap z.1.1.2.2.1 z.1.1.2.2.2 u=z.1.2 ∧ contractMap z.1.1.2.2.1 z.1.1.2.2.2 v=z.2
        then get z.1.1.2.1 u v else 0)).sum)).sum)
  · fun_prop
  · have hs := doubleNatSum
      (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => z.1.1.1)
      (fun z : ((((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ)×ℕ)×ℕ =>
        if decide (contractMap z.1.1.1.1.2.2.1 z.1.1.1.1.2.2.2 z.1.2=z.1.1.1.2) &&
          decide (contractMap z.1.1.1.1.2.2.1 z.1.1.1.1.2.2.2 z.2=z.1.1.2)
        then get z.1.1.1.1.2.1 z.1.2 z.2 else 0)
      (by fun_prop) (by fun_prop)
    have h : Poly (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => if decide (z.1.2=z.2) then 0 else
        (tab z.1.1.1 (fun u => (tab z.1.1.1 (fun v =>
          if decide (contractMap z.1.1.2.2.1 z.1.1.2.2.2 u=z.1.2) && decide (contractMap z.1.1.2.2.1 z.1.1.2.2.2 v=z.2)
          then get z.1.1.2.1 u v else 0)).sum)).sum) := by
      fun_prop
    exact h.congr (fun z => by simp only [decide_eq_true_eq,Bool.and_eq_true])
@[fun_prop] theorem lift_poly : Poly (fun z : ℕ×(Cut×(ℕ×Cut)) => lift z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold lift
  exact Poly.rawTab Prod.fst
    (fun z : (ℕ×(Cut×(ℕ×Cut)))×ℕ => mem z.1.2.2.2 (contractMap z.1.2.1 z.1.2.2.1 z.2))
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem cheaper_poly : Poly (fun z : ℕ×(Matrix ℕ×(Cut×Cut)) => cheaper z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold cheaper
  have h : Poly (fun z : ℕ×(Matrix ℕ×(Cut×Cut)) =>
      if decide (cutCapacity z.1 z.2.1 z.2.2.1≤cutCapacity z.1 z.2.1 z.2.2.2) then z.2.2.1 else z.2.2.2) := by fun_prop
  exact h.congr (fun _ => by simp)
end BinaryMatching.Raw.Compiler
end

end OAI
