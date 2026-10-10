import Mathlib
import OAI.Combinatorics.KMedian.Machines.BinaryReindex
import OAI.Combinatorics.KMedian.Machines.Hardcoded

namespace OAI

section Inline_PCPRawCSP
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable instance relationCoding (A : Type) [Fintype A] : Coding (Finset (A × A)) := finiteCoding _
noncomputable instance relationHardcoded (A : Type) [Fintype A] : Hardcoded (Finset (A × A)) :=
  ⟨fun _ _ _ f => finite_function f⟩
abbrev CSPRow (A : Type) := ℕ × ℕ × Finset (A × A)
abbrev CSPTable (A : Type) := List Unit × List (CSPRow A)
lemma csp_ext {V E A : Type} {C D : BinaryCSP V E A}
    (hl : C.left=D.left) (hr : C.right=D.right) (ha : C.allowed=D.allowed) : C=D := by
  cases C; cases D; simp_all
namespace CSPTable
variable {A : Type} [Fintype A] [DecidableEq A]
def WellFormed (t : CSPTable A) : Prop :=
  0<t.2.length ∧ ∀ e∈t.2, e.1<t.1.length ∧ e.2.1<t.1.length
noncomputable def csp (t : CSPTable A) (h : WellFormed t) :
    BinaryCSP (Fin t.1.length) (Fin t.2.length) A where
  left e := ⟨t.2[e.val].1,(h.2 _ (List.getElem_mem e.isLt)).1⟩
  right e := ⟨t.2[e.val].2.1,(h.2 _ (List.getElem_mem e.isLt)).2⟩
  allowed e := t.2[e.val].2.2
variable {V E : Type} [Fintype V] [Fintype E]
structure Represents (t : CSPTable A) (C : BinaryCSP V E A) where
  vertex : V ≃ Fin t.1.length
  edge : E ≃ Fin t.2.length
  row : ∀ e, t.2[(edge e).val]=((vertex (C.left e)).val,(vertex (C.right e)).val,C.allowed e)
omit [Fintype A] [DecidableEq A] [Fintype V] in
lemma Represents.wellFormed [Nonempty E] {t : CSPTable A} {C : BinaryCSP V E A}
    (r : t.Represents C) : t.WellFormed := by
  constructor
  · have h := Fintype.card_pos (α := E)
    have he := Fintype.card_congr r.edge
    simp only [Fintype.card_fin] at he
    omega
  · intro e he
    obtain ⟨i,hi,hi'⟩ := List.mem_iff_getElem.mp he
    obtain ⟨j,hj⟩ := r.edge.surjective ⟨i,hi⟩
    have hr := r.row j
    simp only [hj] at hr
    rw [← hi',hr]
    exact ⟨(r.vertex (C.left j)).isLt,(r.vertex (C.right j)).isLt⟩
omit [Fintype A] [DecidableEq A] [Fintype V] [Fintype E] in
lemma Represents.csp_eq {t : CSPTable A} {C : BinaryCSP V E A}
    (r : t.Represents C) (h : t.WellFormed) : t.csp h=C.reindex r.vertex r.edge := by
  cases C with
  | mk l rr aa =>
    apply csp_ext
    · funext i
      apply Fin.ext
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg Prod.fst hr
    · funext i
      apply Fin.ext
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg (fun x : CSPRow A => x.2.1) hr
    · funext i
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg (fun x : CSPRow A => x.2.2) hr
noncomputable def self_represents (t : CSPTable A) (h : t.WellFormed) : t.Represents (t.csp h) :=
  ⟨Equiv.refl _,Equiv.refl _,fun _ => rfl⟩
noncomputable def row (t : CSPTable A) (e : ℕ) : CSPRow A := t.2[e]?.getD (0,0,∅)
omit [DecidableEq A] in
lemma poly_row : Poly (fun p : CSPTable A × ℕ => row p.1 p.2) := by
  unfold row
  fun_prop
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawCSP

end OAI
