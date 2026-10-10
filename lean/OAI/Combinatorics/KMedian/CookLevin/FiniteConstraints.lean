import Mathlib
import OAI.Combinatorics.KMedian.PCP.AlphabetReduction

namespace OAI

section Inline_PCPFiniteConstraints

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

structure FiniteCSP (V T Q A : Type) where
  query : T → Q → V
  accept : T → Finset (Q → A)
namespace FiniteCSP
variable {V T Q A : Type} [Fintype Q] [Fintype A] [DecidableEq A]
variable [Nonempty Q] [Inhabited A]
variable (C : FiniteCSP V T Q A)
def Satisfies (a : V → A) : Prop := ∀ t, (a ∘ C.query t)∈C.accept t
abbrev Label := A ⊕ (Q → A)
noncomputable def binary : BinaryCSP (V ⊕ T) (T × Q) (Label (Q := Q) (A := A)) where
  left t := .inl (C.query t.1 t.2)
  right t := .inr t.1
  allowed t := univ.filter (fun p => ∃ a b, p=(Sum.inl a,Sum.inr b) ∧
    b∈C.accept t.1 ∧ a=b t.2)
def honest (a : V → A) : V ⊕ T → Label (Q := Q) (A := A) :=
  Sum.elim (fun v => .inl (a v)) (fun t => .inr (a ∘ C.query t))
omit [Nonempty Q] [Inhabited A] in
lemma binary_complete (a : V → A) (h : C.Satisfies a) : C.binary.Satisfies (C.honest a) := by
  rintro ⟨t,i⟩
  simp only [binary,mem_filter,mem_univ,true_and,honest,Sum.elim_inl,Sum.elim_inr]
  exact ⟨a (C.query t i),a ∘ C.query t,rfl,h t,rfl⟩
def decoded (a : V ⊕ T → Label (Q := Q) (A := A)) : V → A :=
  fun v => (a (.inl v)).elim id (fun _ => default)
lemma binary_sound (a : V ⊕ T → Label (Q := Q) (A := A)) (h : C.binary.Satisfies a) :
    C.Satisfies (decoded a) := by
  intro t
  have hh (i : Q) : ∃ x b, (a (.inl (C.query t i)),a (.inr t))=(.inl x,.inr b) ∧
      b∈C.accept t ∧ x=b i := by
    simpa only [binary,mem_filter,mem_univ,true_and] using h (t,i)
  obtain ⟨x,b,hb,hmem,hx⟩ := hh (Classical.arbitrary Q)
  have he : decoded a ∘ C.query t=b := by
    funext i
    obtain ⟨y,c,hc,hcm,hy⟩ := hh i
    have hc' : c=b := Sum.inr.inj ((congrArg Prod.snd hc).symm.trans (congrArg Prod.snd hb))
    subst c
    change (a (.inl (C.query t i))).elim id (fun _ => default)=b i
    have hc0 : a (.inl (C.query t i))=Sum.inl y := congrArg Prod.fst hc
    rw [hc0]
    exact hy
  rw [he]
  exact hmem
lemma binary_iff : (∃ a, C.binary.Satisfies a) ↔ ∃ a, C.Satisfies a := by
  constructor
  · rintro ⟨a,ha⟩; exact ⟨decoded a,C.binary_sound a ha⟩
  · rintro ⟨a,ha⟩; exact ⟨C.honest a,C.binary_complete a ha⟩
end FiniteCSP
namespace BinaryCSP
variable {V E A B : Type} [DecidableEq A] [Fintype B]
variable (C : BinaryCSP V E A) (decode : B → A)
noncomputable def pullLabels : BinaryCSP V E B where
  left := C.left
  right := C.right
  allowed e := univ.filter (fun p => (decode p.1,decode p.2)∈C.allowed e)
lemma pullLabels_satisfies (a : V → B) :
    (C.pullLabels decode).Satisfies a ↔ C.Satisfies (decode ∘ a) := by
  simp only [Satisfies,pullLabels,mem_filter,mem_univ,true_and,Function.comp_def]
lemma pullLabels_complete (encode : A → B) (he : Function.LeftInverse decode encode)
    (a : V → A) (h : C.Satisfies a) : (C.pullLabels decode).Satisfies (encode ∘ a) := by
  apply (C.pullLabels_satisfies decode _).mpr
  intro e
  change (decode (encode (a (C.left e))), decode (encode (a (C.right e))))∈C.allowed e
  rw [he _,he _]
  exact h e
end BinaryCSP
end MetricKMedian.PCP

end Inline_PCPFiniteConstraints

end OAI
