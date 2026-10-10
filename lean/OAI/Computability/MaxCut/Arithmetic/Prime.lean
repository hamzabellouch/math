import Mathlib
import OAI.Computability.MaxCut.Machines.FramedLen
import OAI.Computability.MaxCut.Estimates.ListSum

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr.Represented
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {f g : List Bool → (ℕ → ℕ) → ℕ}
theorem prime (hf : Represented f) : Represented (fun s a => if (f s a).Prime then 1 else 0) := by
  obtain ⟨e,he⟩ := hf; exact ⟨Expr.prime e, by intros; simp [he]⟩
theorem framedLen (hf : Represented f) : Represented (fun s a => 2*(f s a).size+1) := by
  obtain ⟨e,he⟩ := hf; exact ⟨Expr.framedLen e, by intros; simp [he]⟩
theorem framedBit (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => if g s a < 2*(f s a).size then
      if g s a % 2=0 then 1 else f s a / 2^(g s a/2)%2 else 0) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨Expr.framedBit e d, by intros; simp [Expr.framedBit_eval,he,hd]⟩
theorem iteLt {h j : List Bool → (ℕ → ℕ) → ℕ}
    (hf : Represented f) (hg : Represented g) (hh : Represented h) (hj : Represented j) :
    Represented (fun s a => if f s a<g s a then h s a else j s a) := by
  exact (cond (lt hf hg) hh hj).congr (by intros; split_ifs <;> simp_all)
theorem searchPrime (hf : Represented f) : Represented (fun s a => Unweighted.searchPrime (f s a)) := by
  obtain ⟨e,he⟩ := hf
  let b : Expr := .add (.mul (.const 2) (.add e (.const 1))) (.const 1)
  let p : Expr := .mul (Expr.lt (.add (e.rename Nat.succ) (.const 1)) (.arg 0)) (Expr.prime (.arg 0))
  refine ⟨least b p, ?_⟩
  intro s a
  let m := f s a
  have hs : ((List.range (2*(m+1)+1)).find? (fun q => decide (m+1<q ∧ q.Prime))).isSome := by
    obtain ⟨q,hq,hm,hb⟩ := Nat.exists_prime_lt_and_le_two_mul (m+1) (by omega)
    exact List.find?_isSome.mpr ⟨q,List.mem_range.mpr (by omega),by simp [hm,hq]⟩
  cases hh : ((List.range (2*(m+1)+1)).find? (fun q => decide (m+1<q ∧ q.Prime))) with
  | none => rw [hh] at hs; contradiction
  | some k =>
    have hp := List.find?_eq_some_iff_getElem.mp hh
    obtain ⟨i,hi,hik,hmin⟩ := hp.2
    have hik' : i=k := by simpa using hik
    subst i
    have hk : k<2*(m+1)+1 := by simpa using hi
    have hp' : m+1<k ∧ k.Prime := by simpa using hp.1
    change (least b p).eval s a = Unweighted.searchPrime m
    rw [Unweighted.searchPrime, hh]
    apply least_eq
    · simpa [b,eval,he,m] using hk
    · simp [p,eval,lt_eval,prime_eval,rename_eval,bind,he,hp',m]
    · intro j hj
      have hmin' : ¬ (m+1<j ∧ j.Prime) := by
        intro hbad
        have hh' := hmin j hj
        simp [hbad] at hh'
      simp only [p,eval,lt_eval,prime_eval,rename_eval,bind,he]
      by_cases hl : m+1<j <;> by_cases hp : j.Prime <;> simp_all [m]

end OptimalMaxCut.CounterMachine.Expr.Represented

end

end OAI
