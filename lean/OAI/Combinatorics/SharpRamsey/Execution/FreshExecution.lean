import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.FreshFamilies
import OAI.Combinatorics.SharpRamsey.Trees.ChronologicalTree

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I]
variable {α : I→Type*}

def arrive (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (target : I) :
    BinaryTree I→Domains A B→Option (Domains A B)
  | .nil,_=>none
  | .node i l r,U=>if i=target then some U else
      match choose i (z i) U with
      | none=>none
      | some c=>
        let V:=read i (z i) U c
        (arrive choose read z target l (V.1,U.2)).orElse
          (fun _=>arrive choose read z target r (U.1,V.2))

theorem arrive_congr (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z z' : ∀ i,α i) (target : I)
    (hz : ∀ j,j≠target→z j=z' j) (t : BinaryTree I) (U : Domains A B) :
    arrive choose read z target t U=arrive choose read z' target t U := by
  induction t generalizing U with
  | nil=>rfl
  | node i l r hl hr=>
    simp only [arrive]
    split_ifs with hi
    · rfl
    · rw [hz i hi]
      cases choose i (z' i) U with
      | none=>rfl
      | some c=>
        simp only
        rw [hl,hr]

def outsideState (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I) (dummy : α target)
    (t : BinaryTree I) (U : Domains A B) (s : Outside (α:=α) target) :
    Option (Domains A B) :=
  arrive choose read ((Equiv.piSplitAt target α).symm (dummy,s)) target t U

theorem arrive_outside (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I) (dummy : α target)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) :
    arrive choose read z target t U=
      outsideState choose read target dummy t U (outside target z) := by
  apply arrive_congr
  intro j hj
  simp only [Equiv.piSplitAt_symm_apply,dite_eq_right hj,outside]

def produced (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I)
    (f : Domains A B→α target→ℝ) (t : BinaryTree I) (U : Domains A B)
    (z : ∀ i,α i) : ℝ :=
  match arrive choose read z target t U with
  | none=>0
  | some V=>f V (z target)

variable [Fintype I] [∀ i,Fintype (α i)]

theorem produced_bound (p : ∀ i,Law (α i))
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I) (dummy : α target)
    (f : Domains A B→α target→ℝ) (t : BinaryTree I) (U : Domains A B)
    (B₀ : ℝ) (hB : 0≤B₀)
    (hlocal : ∀ V,(∑ x,(p target).mass x*f V x)≤B₀) :
    (∑ z,(piLaw p).mass z*produced choose read target f t U z)≤B₀ := by
  let g := fun s : Outside (α:=α) target=>fun x : α target=>
    match outsideState choose read target dummy t U s with
    | none=>0
    | some V=>f V x
  have he (z : ∀ i,α i) : produced choose read target f t U z=
      g (outside target z) (z target) := by
    unfold produced g
    rw [arrive_outside choose read target dummy]
  simp_rw [he]
  rw [family_integral]
  calc
    _ ≤ ∑ s,(outsideLaw p target).mass s*B₀ := by
      apply sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ ((outsideLaw p target).nonneg s)
      dsimp only [g]
      cases outsideState choose read target dummy t U s with
      | none=>simpa only [mul_zero,sum_const_zero] using hB
      | some V=>exact hlocal V
    _ = B₀ := by rw [←sum_mul,(outsideLaw p target).total,one_mul]

def fixedRead (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) :
    CapReader A B (I×C) := fun U c=>read c.1 (z c.1) U c.2

def fixedChoose (choose : ∀ i,α i→Domains A B→Option C) (z : ∀ i,α i) :
    I→Domains A B→Option (I×C) := fun i U=>(choose i (z i) U).map (fun c=>(i,c))

omit [DecidableEq I] [Fintype I] [∀ i,Fintype (α i)] in

theorem fixed_decoder_correct (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i)
    (targets : I→List (A×B)) (counts : I→ℕ) (t : BinaryTree I) (U : Domains A B) :
    let tr:=execute (fixedRead read z) (fixedChoose choose z) t U
    List.Forall₂ (fun x D=>x∈D)
      (output R (fixedRead read z) targets counts tr U)
      (decode R (fixedRead read z)
        (message R (fixedRead read z) targets counts tr U) U) := by
  exact decoder_correct R (fixedRead read z) targets counts _ U

end
end SharpLogRamsey.FreshExecution

end

end OAI
