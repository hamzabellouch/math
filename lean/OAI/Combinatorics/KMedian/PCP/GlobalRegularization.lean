import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PaddingSound
import OAI.Combinatorics.KMedian.Amplification.RegularizationSound

namespace OAI

section Inline_PCPGlobalRegularization

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace GlobalRegularization
variable {V E A : Type} [Fintype E] [Nonempty E]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)

noncomputable def depth := ExpanderFamily.level (Fintype.card (CloudCopies.Node C)-1)
abbrev Node := ExpanderFamily.Vertex (depth C)
abbrev FastPort := ExpanderFamily.Degree × ExpanderFamily.Degree
abbrev StrongPort := FastPort × FastPort
abbrev Degree := PortGraph.BlendPort (D := CloudCopies.RegularPort) (S := StrongPort)

omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma node_lower : Fintype.card (CloudCopies.Node C) ≤ Fintype.card (Node C) := by
  have h := ExpanderFamily.padding_lower (Fintype.card (CloudCopies.Node C)-1)
  have hp := Fintype.card_pos (α := CloudCopies.Node C)
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [Node,depth,← Nat.card_eq_fintype_card,Nat.sub_add_cancel hp] using h

omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma node_relative_upper : Fintype.card (Node C) ≤
    ExpanderFamily.growth*Fintype.card (CloudCopies.Node C) := by
  have h := ExpanderFamily.padding_upper (Fintype.card (CloudCopies.Node C)-1)
  have hp := Fintype.card_pos (α := CloudCopies.Node C)
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [Node,depth,← Nat.card_eq_fintype_card,Nat.sub_add_cancel hp] using h

omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma node_upper : Fintype.card (Node C) ≤ 2*ExpanderFamily.growth^2*Fintype.card E := by
  calc
    _ ≤ ExpanderFamily.growth*Fintype.card (CloudCopies.Node C) := node_relative_upper C
    _ ≤ ExpanderFamily.growth*(2*ExpanderFamily.growth*Fintype.card E) :=
      Nat.mul_le_mul_left _ (CloudCopies.node_card_upper C)
    _ = _ := by ring

noncomputable def embed : CloudCopies.Node C ↪ Node C :=
  (Fintype.equivFin _).toEmbedding.trans ((Fin.castLEEmb (node_lower C)).trans
    (Fintype.equivFin _).symm.toEmbedding)

noncomputable def strong : PortGraph (Node C) StrongPort :=
  (ExpanderFamily.graph (depth C)).square.square

omit [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
lemma strong_contracts : (strong C).Contracts (1/16) := by
  have h := ((ExpanderFamily.graph (depth C)).square).square_contracts
    ((ExpanderFamily.graph (depth C)).square_contracts (ExpanderFamily.graph_contracts _))
  norm_num at h
  exact h

noncomputable def padded : PortCSP ((CloudCopies.regularGraph C).extend (embed C)) A :=
  (CloudCopies.regularCSP C).extend (embed C)
noncomputable def graph : PortGraph (Node C) Degree :=
  ((CloudCopies.regularGraph C).extend (embed C)).blend (strong C)
noncomputable def csp : PortCSP (graph C) A :=
  (padded C).blend (PortCSP.always (strong C))

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem contracts : (graph C).Contracts (1/2) :=
  PortGraph.blend_half _ _ (strong_contracts C)

noncomputable def decoded (a : Node C → A) : V → A :=
  CloudCopies.decoded C (a ∘ embed C)

theorem complete (x : V → A) (hx : C.Satisfies x) : ∃ a, (csp C).Satisfies a := by
  obtain ⟨a,ha⟩ := (CloudCopies.regularCSP C).extend_complete (embed C)
    (CloudCopies.honest C x) (CloudCopies.regular_complete C x hx)
  exact ⟨a,PortCSP.blend_complete _ _ a ha (PortCSP.always_complete _ a)⟩

theorem sound (a : Node C → A) : C.rejection (decoded C a) ≤
    (18*(ExpanderFamily.growth:ℝ)^2)*testRate ((csp C).Bad a) := by
  have hr := CloudCopies.regular_sound C (a ∘ embed C)
  have hp := (CloudCopies.regularCSP C).extend_failure_mass (embed C) a
  have hm := PortCSP.blend_failure (padded C) (PortCSP.always (strong C)) a
  rw [PortCSP.always_failure, mul_zero,add_zero] at hm
  change testRate ((csp C).Bad a)=testRate ((padded C).Bad a)/3 at hm
  change (Fintype.card (Node C):ℝ)*testRate ((padded C).Bad a)=_ at hp
  have hs : (Fintype.card (Node C):ℝ) ≤
      (ExpanderFamily.growth:ℝ)*Fintype.card (CloudCopies.Node C) := by
    exact_mod_cast node_relative_upper C
  have hn := testRate_nonneg ((padded C).Bad a)
  have hv : 0 < (Fintype.card (CloudCopies.Node C):ℝ) := by positivity
  have hl : testRate ((CloudCopies.regularCSP C).Bad (a ∘ embed C)) ≤
      (ExpanderFamily.growth:ℝ)*testRate ((padded C).Bad a) := by
    apply (mul_le_mul_iff_right₀ hv).mp
    nlinarith only [hp,mul_le_mul_of_nonneg_right hs hn]
  change C.rejection (CloudCopies.decoded C (a ∘ embed C)) ≤ _
  have hg : 0 ≤ (ExpanderFamily.growth:ℝ) := Nat.cast_nonneg _
  nlinarith only [hr,mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num : (0:ℝ)≤6) hg),hm]

end GlobalRegularization
end MetricKMedian.PCP

end Inline_PCPGlobalRegularization

end OAI
