import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringObjects
import OAI.Combinatorics.KMedian.PCP.BinaryReduction
import OAI.Combinatorics.KMedian.Projection.IncidenceOperator
import OAI.Combinatorics.KMedian.Projection.Rounding
import OAI.Combinatorics.KMedian.Projection.Repeat
import OAI.Combinatorics.KMedian.Projection.IncidenceExpansion

namespace OAI

section Inline_PCPCSPProjection

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D} [DecidableEq A]
variable (C : PortCSP G A)
def Legal (p : V × D) (a : A × A) : Prop :=
  a ∈ C.allowed p ∧ ((G.rotate p).1=p.1 → a.1=a.2)
variable (chosen : V × D → A × A) (hchosen : ∀ p, C.Legal p (chosen p))
noncomputable def repair (p : V × D) (a : A × A) : A × A := if C.Legal p a then a else chosen p
omit [DecidableEq A]
include hchosen in
lemma repair_legal (p : V × D) (a : A × A) : C.Legal p (C.repair chosen p a) := by
  unfold repair
  split_ifs with h
  · exact h
  · exact hchosen p
lemma repair_fixed (p : V × D) (a : A × A) (h : C.Legal p a) : C.repair chosen p a=a := ite_eq_left h
noncomputable def projection : BiProjection (V × D) V Bool (D × Bool) (A × A) A :=
  G.incidence (fun q a => if q.2 then (C.repair chosen q.1 a).2 else (C.repair chosen q.1 a).1)

lemma projection_complete (x : V → A) (hx : C.Satisfies x) : (C.projection chosen).Perfect := by
  refine ⟨fun p => (x p.1,x (G.rotate p).1),x,?_⟩
  intro p b
  have hl : C.Legal p (x p.1,x (G.rotate p).1) := ⟨hx p.1 p.2,by intro h; rw [h]⟩
  cases b <;> simp only [projection,PortGraph.incidence,PortGraph.incidenceEdge,
    Bool.false_eq_true,ite_false,ite_true,repair_fixed C chosen p _ hl] <;> rfl

include hchosen in
lemma projection_consistent : (C.projection chosen).Consistent := by
  intro p b c h a
  have hl := (C.repair_legal chosen hchosen p a).2
  cases b <;> cases c
  · rfl
  · have he : p.1=(G.rotate p).1 := h
    exact hl he.symm
  · have he : (G.rotate p).1=p.1 := h
    exact (hl he).symm
  · rfl

include hchosen in
lemma reject_incidence (x : V → A) (a : V × D → A × A) (p : V × D) (hp : C.Bad x p) :
    ∃ b : Bool, (C.projection chosen).project (p,b) (a p) ≠
      x ((C.projection chosen).edge (p,b)).1 := by
  by_contra h
  push Not at h
  have h0 : (C.repair chosen p (a p)).1=x p.1 := h false
  have h1 : (C.repair chosen p (a p)).2=x (G.rotate p).1 := h true
  have hm := (C.repair_legal chosen hchosen p (a p)).1
  have he : C.repair chosen p (a p)=(x p.1,x (G.rotate p).1) := Prod.ext h0 h1
  rw [he] at hm
  exact hp hm

variable [Fintype V] [Fintype D] [Fintype A] [Nonempty V] [Nonempty D] [Nonempty A]
omit [Fintype A] [Nonempty A]
include hchosen in
lemma projection_sound (δ : ℝ) (hδ : ∀ x : V → A, δ≤testRate (C.Bad x)) :
    (C.projection chosen).Sound (1-δ/2) := by
  intro a x
  let R : (V × D) → Bool → Prop := fun p b => (C.projection chosen).project (p,b) (a p) ≠
      x ((C.projection chosen).edge (p,b)).1
  have hp (p : V × D) : (@ite ℝ (C.Bad x p) (Classical.propDecidable _) 1 0)/2 ≤ testRate (R p) := by
    split_ifs with h
    · obtain ⟨b,hb⟩ := C.reject_incidence chosen hchosen x a p h
      simpa only [Fintype.card_bool,Nat.cast_ofNat] using testRate_ge_atom (R p) b hb
    · exact (by simpa using testRate_nonneg (R p))
  have hav := expect_le_expect (s := (univ : Finset (V × D))) (fun p _ => hp p)
  rw [← expect_div] at hav
  have he : (C.projection chosen).score a x + (𝔼 p, testRate (R p))=1 := by
    unfold BiProjection.score
    rw [← expect_add_distrib]
    calc
      _ = 𝔼 _p : V × D, (1:ℝ) := by
        apply expect_congr rfl
        intro p _
        simpa only [testRate,R] using testRate_complement (fun b : Bool =>
          (C.projection chosen).project (p,b) (a p)=x ((C.projection chosen).edge (p,b)).1)
      _ = 1 := Fintype.expect_const 1
  have hav' : testRate (C.Bad x)/2≤𝔼 p, testRate (R p) := by
    simpa only [testRate] using hav
  linarith only [hδ x,hav',he]

lemma projection_expands (hG : G.Contracts (1/2)) : (C.projection chosen).Expands (1/4) :=
  G.incidence_expands hG _
end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPProjection

end OAI
