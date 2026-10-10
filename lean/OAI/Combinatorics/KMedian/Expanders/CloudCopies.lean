import Mathlib
import OAI.Combinatorics.KMedian.Expanders.EqualityExpansion
import OAI.Combinatorics.KMedian.Expanders.ExpanderFamily
import OAI.Combinatorics.KMedian.PCP.AlphabetReduction

namespace OAI

section Inline_PCPCloudCopies

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
abbrev Dart := E × Bool

def endpoint (d : Dart (E := E)) : V := if d.2 then C.right d.1 else C.left d.1
abbrev Active := Set.range (endpoint C)
def owner (d : Dart (E := E)) : Active C := ⟨endpoint C d,Set.mem_range_self d⟩

omit [Fintype V] [Fintype E] in
lemma owner_surjective : Function.Surjective (owner C) := by
  rintro ⟨v,d,hd⟩
  exact ⟨d,Subtype.ext hd⟩

abbrev Incident (v : Active C) := {d : Dart (E := E) // owner C d=v}
instance incidentNonempty (v : Active C) : Nonempty (Incident C v) := by
  obtain ⟨d,hd⟩ := owner_surjective C v
  exact ⟨⟨d,hd⟩⟩

noncomputable def depth (v : Active C) := ExpanderFamily.level (Fintype.card (Incident C v)-1)
abbrev Copy (v : Active C) := ExpanderFamily.Vertex (depth C v)
abbrev Node := (v : Active C) × Copy C v

omit [Fintype V] in
lemma copy_card_lower (v : Active C) : Fintype.card (Incident C v) ≤ Fintype.card (Copy C v) := by
  have h := ExpanderFamily.padding_lower (Fintype.card (Incident C v)-1)
  have hp := Fintype.card_pos (α := Incident C v)
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [Copy,depth,← Nat.card_eq_fintype_card,Nat.sub_add_cancel hp] using h

omit [Fintype V] in
lemma copy_card_upper (v : Active C) : Fintype.card (Copy C v) ≤
    ExpanderFamily.growth*Fintype.card (Incident C v) := by
  have h := ExpanderFamily.padding_upper (Fintype.card (Incident C v)-1)
  have hp := Fintype.card_pos (α := Incident C v)
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [Copy,depth,← Nat.card_eq_fintype_card,Nat.sub_add_cancel hp] using h

noncomputable def incidentEmbed (v : Active C) : Incident C v ↪ Copy C v :=
  (Fintype.equivFin _).toEmbedding.trans ((Fin.castLEEmb (copy_card_lower C v)).trans
    (Fintype.equivFin _).symm.toEmbedding)

noncomputable def dartEmbed : Dart (E := E) ↪ Node C where
  toFun d := ⟨owner C d, incidentEmbed C (owner C d) ⟨d,rfl⟩⟩
  inj' := by
    intro d e h
    have ho : owner C d=owner C e := congrArg Sigma.fst h
    have hh : (⟨owner C d,⟨d,rfl⟩⟩ : (v : Active C) × Incident C v) =
        ⟨owner C e,⟨e,rfl⟩⟩ := by
      apply (Function.Embedding.sigmaMap (Function.Embedding.refl _) (incidentEmbed C)).injective
      exact h
    exact congrArg (fun p : (v : Active C) × Incident C v => p.2.val) hh

omit [Fintype V] in
lemma node_card_upper : Fintype.card (Node C) ≤ 2*ExpanderFamily.growth*Fintype.card E := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ v : Active C, ExpanderFamily.growth*Fintype.card (Incident C v) :=
      sum_le_sum (fun v _ => copy_card_upper C v)
    _ = ExpanderFamily.growth*Fintype.card ((v : Active C) × Incident C v) := by
      rw [← mul_sum,Fintype.card_sigma]
    _ = _ := by
      rw [Fintype.card_congr (Equiv.sigmaFiberEquiv (owner C)),Fintype.card_prod,Fintype.card_bool]
      ring

noncomputable instance activeNonempty [Nonempty E] : Nonempty (Active C) :=
  ⟨owner C (Classical.arbitrary E,false)⟩

noncomputable instance nodeNonempty [Nonempty E] : Nonempty (Node C) := by
  let v := Classical.arbitrary (Active C)
  exact ⟨⟨v,Classical.arbitrary (Copy C v)⟩⟩

noncomputable def equalityRotate (p : Node C × ExpanderFamily.Degree) : Node C × ExpanderFamily.Degree :=
  (⟨p.1.1,(ExpanderFamily.graph (depth C p.1.1)).step p.1.2 p.2⟩,
    (ExpanderFamily.graph (depth C p.1.1)).back p.1.2 p.2)

omit [Fintype V] in
lemma equalityRotate_involutive : Function.Involutive (equalityRotate C) := by
  rintro ⟨⟨v,w⟩,d⟩
  simp only [equalityRotate,PortGraph.step_back,PortGraph.back_back]

noncomputable def equalityGraph : PortGraph (Node C) ExpanderFamily.Degree where
  rotate := { toFun := equalityRotate C
              invFun := equalityRotate C
              left_inv := equalityRotate_involutive C
              right_inv := equalityRotate_involutive C }
  involutive := equalityRotate_involutive C

omit [Fintype V] in
@[simp] lemma equality_step (v : Active C) (w : Copy C v) (d : ExpanderFamily.Degree) :
    (equalityGraph C).step ⟨v,w⟩ d=⟨v,(ExpanderFamily.graph (depth C v)).step w d⟩ := rfl

variable [Fintype A] [Inhabited A] [DecidableEq A]
noncomputable def decoded (a : Node C → A) (v : V) : A :=
  if h : v ∈ Set.range (endpoint C) then
    PortGraph.majorityLabel (fun w : Copy C ⟨v,h⟩ => a ⟨⟨v,h⟩,w⟩) else default

omit [Fintype V] [DecidableEq A] in
lemma decoded_active (a : Node C → A) (v : Active C) :
    decoded C a v.val=PortGraph.majorityLabel (fun w : Copy C v => a ⟨v,w⟩) := by
  simp [decoded,v.property]

omit [Fintype V] [DecidableEq A] in
theorem cloud_sound (a : Node C → A) (v : Active C) :
    testRate (fun w : Copy C v => a ⟨v,w⟩ ≠ decoded C a v.val) ≤
      2*(ExpanderFamily.graph (depth C v)).equalityFailure (fun w => a ⟨v,w⟩) := by
  rw [decoded_active]
  exact PortGraph.equality_cloud_sound _ (fun w => a ⟨v,w⟩) (ExpanderFamily.graph_contracts _)

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPCloudCopies

end OAI
