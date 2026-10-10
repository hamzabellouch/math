import Mathlib
import OAI.Combinatorics.KMedian.Amplification.CSPMix
import OAI.Combinatorics.KMedian.Expanders.CloudCopies
import OAI.Combinatorics.KMedian.Expanders.GraphExtend

namespace OAI

section Inline_PCPRegularizationObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
variable (C : BinaryCSP V E A)

def dartFlip : Dart (E := E) ≃ Dart (E := E) where
  toFun d := (d.1,!d.2)
  invFun d := (d.1,!d.2)
  left_inv d := by simp
  right_inv d := by simp

def dartGraph : PortGraph (Dart (E := E)) Unit where
  rotate := dartFlip.prodCongr (Equiv.refl Unit)
  involutive := by rintro ⟨⟨e,b⟩,u⟩; simp [dartFlip]

def dartCSP : PortCSP (dartGraph (E := E)) A where
  allowed p := univ.filter (fun q => if p.1.2 then (q.2,q.1) ∈ C.allowed p.1.1
    else q ∈ C.allowed p.1.1)
  symmetric := by
    rintro ⟨⟨e,b⟩,u⟩ a b'
    cases b <;> simp [dartGraph,dartFlip]

noncomputable def matchingGraph : PortGraph (Node C) Unit := dartGraph.extend (dartEmbed C)
noncomputable def matchingCSP : PortCSP (matchingGraph C) A := (dartCSP C).extend (dartEmbed C)

@[simp] lemma matching_bad (a : Node C → A) (e : E) :
    (matchingCSP C).Bad a (dartEmbed C (e,false),()) ↔
      (a (dartEmbed C (e,false)),a (dartEmbed C (e,true))) ∉ C.allowed e := by
  change ((dartCSP C).extend (dartEmbed C)).Bad a (dartEmbed C (e,false),()) ↔ _
  rw [PortCSP.extend_bad_image (dartCSP C) (dartEmbed C) a ((e,false),())]
  simp [PortCSP.Bad,dartCSP,dartGraph,PortGraph.step,dartFlip]

noncomputable def equalityCSP : PortCSP (equalityGraph C) A where
  allowed _ := univ.filter (fun q => q.1=q.2)
  symmetric _ a b := by simp [eq_comm]

@[simp] lemma equality_bad (a : Node C → A) (v : Active C) (w : Copy C v)
    (d : ExpanderFamily.Degree) :
    (equalityCSP C).Bad a (⟨v,w⟩,d) ↔
      a ⟨v,w⟩ ≠ a ⟨v,(ExpanderFamily.graph (depth C v)).step w d⟩ := by
  simp [PortCSP.Bad,equalityCSP]

abbrev RegularPort := PortGraph.BlendPort (D := Unit) (S := ExpanderFamily.Degree)
noncomputable def regularGraph : PortGraph (Node C) RegularPort := (matchingGraph C).blend (equalityGraph C)
noncomputable def regularCSP : PortCSP (regularGraph C) A := (matchingCSP C).blend (equalityCSP C)

def honest (x : V → A) (n : Node C) : A := x n.1.val

omit [Fintype A] [DecidableEq A] in
@[simp] lemma honest_dart (x : V → A) (d : Dart (E := E)) :
    honest C x (dartEmbed C d)=x (endpoint C d) := rfl

lemma equality_complete (x : V → A) : (equalityCSP C).Satisfies (honest C x) := by
  rintro ⟨v,w⟩ d
  simp [equalityCSP,honest,equality_step]

lemma matching_complete (x : V → A) (hx : C.Satisfies x) :
    (matchingCSP C).Satisfies (honest C x) := by
  intro n d
  by_cases hn : n ∈ Set.range (dartEmbed C)
  · obtain ⟨⟨e,b⟩,rfl⟩ := hn
    change _ ∈ (dartCSP C).extendedAllowed (dartEmbed C) (dartEmbed C (e,b),d)
    rw [PortCSP.extendedAllowed_image (dartCSP C) (dartEmbed C) ((e,b),d)]
    change (honest C x (dartEmbed C (e,b)),
      honest C x (((dartGraph (E := E)).extend (dartEmbed C)).step (dartEmbed C (e,b)) d)) ∈ _
    rw [PortGraph.extend_step_image]
    cases b <;> simpa [dartCSP,dartGraph,PortGraph.step,dartFlip,endpoint] using hx e
  · change _ ∈ (dartCSP C).extendedAllowed (dartEmbed C) (n,d)
    rw [PortCSP.extendedAllowed_outside _ _ (n,d) hn]
    exact mem_univ _

lemma regular_complete (x : V → A) (hx : C.Satisfies x) :
    (regularCSP C).Satisfies (honest C x) :=
  PortCSP.blend_complete _ _ _ (matching_complete C x hx) (equality_complete C x)

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPRegularizationObjects

end OAI
