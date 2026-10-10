import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialLists
import OAI.Analysis.MatrixSigning.Complexity.PolynomialScalar
import OAI.Analysis.MatrixSigning.Realization.FilterRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
lemma foldl_property {f : β → α → β} (P : β → Prop) (xs : List α) (s : β)
    (hs : P s) (hf : ∀ x∈xs,∀a,P a → P (f a x)) : P (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih => exact ih (f s x) (hf x (by simp) s hs) (fun y hy => hf y (by simp [hy]))
lemma find_fold_size {p : γ×α → Bool} {f : γ×α → β}
    (value : Realizes (prodCode ec ea) eb f) [PolyTime value]
    (r : Realizes (prodCode (prodCode ec eb) ea) (prodCode ec eb)
      (fun z => (z.1.1,if p (z.1.1,z.2) then f (z.1.1,z.2) else z.1.2))) : FoldSize r := by
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=value)
  let U := 3*X+1+q.comp (3*X+1)
  refine ⟨⟨3*X+1+U,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode ec eb) (listCode ea) (s,xs)).length
  have hc : (ec s.1).length≤L := (le_prodCode_left s).trans (le_prodCode_left (s,xs))
  have hb : (eb s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have hv : ∀x∈ys,(eb (f (s.1,x))).length≤U.eval L := by
    intro x hx
    have hl : (prodCode ec ea (s.1,x)).length≤3*L+1 := by
      have he := (mem_length_le_code ys hx).trans hy
      rw [prodCode_length];dsimp only;omega
    have h := (value.output_length (s.1,x)).trans
      (Nat.add_le_add hl ((hq _).trans (q.eval_mono hl)))
    simp only [U,NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
    exact h
  have hh := foldl_property (f:=fun a x => (a.1,if p (a.1,x) then f (a.1,x) else a.2))
    (fun a : γ×β => a.1=s.1 ∧ (eb a.2).length≤L+U.eval L) ys s
    ⟨rfl,hb.trans (Nat.le_add_right _ _)⟩ (by
      intro x hx a ha
      refine ⟨ha.1,?_⟩
      dsimp only
      split
      · rw [ha.1];exact (hv x hx).trans (Nat.le_add_left _ _)
      · exact ha.2)
  rw [prodCode_length,hh.1]
  change _≤3*L+1+U.eval L
  have hb' := hh.2
  dsimp only at *
  omega
instance poly_findValue {p : γ×α → Bool} {f : γ×α → β}
    (test : Realizes (prodCode ec ea) boolCode p) (value : Realizes (prodCode ec ea) eb f)
    [PolyTime test] [PolyTime value] : PolyTime (test.findValue value) := by
  let old := first (prodCode ec eb) ea
  let cx := (old.then (first ec eb)).both (second (prodCode ec eb) ea)
  let body := (old.then (first ec eb)).both ((cx.then test).ite (cx.then value) (old.then (second ec eb)))
  have : FoldSize body := find_fold_size value body
  dsimp only [Realizes.findValue]
  apply poly_congr
end CurrentKS.Realization

end OAI
