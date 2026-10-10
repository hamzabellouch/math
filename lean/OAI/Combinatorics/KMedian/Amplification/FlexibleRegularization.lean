import Mathlib
import OAI.Combinatorics.KMedian.Amplification.FlexibleCloud
import OAI.Combinatorics.KMedian.PCP.GlobalRegularization

namespace OAI

section Inline_PCPFlexibleRegularization

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace FlexibleRegularization
variable {V E A : Type} [Fintype V] [Fintype E] [Nonempty E]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)

open GlobalRegularization

variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ Node C)

noncomputable def padded : PortCSP ((FlexibleCloud.regularGraph C cloudEmbed).extend padEmbed) A :=
  (FlexibleCloud.regularCSP C cloudEmbed).extend padEmbed
noncomputable def graph : PortGraph (Node C) Degree :=
  ((FlexibleCloud.regularGraph C cloudEmbed).extend padEmbed).blend (strong C)
noncomputable def csp : PortCSP (graph C cloudEmbed padEmbed) A :=
  (padded C cloudEmbed padEmbed).blend (PortCSP.always (strong C))

omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
theorem contracts : (graph C cloudEmbed padEmbed).Contracts (1/2) :=
  PortGraph.blend_half _ _ (strong_contracts C)

noncomputable def decoded (a : Node C → A) : V → A :=
  CloudCopies.decoded C (a ∘ padEmbed)

omit [Fintype V] [Nonempty E] in
theorem complete (x : V → A) (hx : C.Satisfies x) : ∃ a, (csp C cloudEmbed padEmbed).Satisfies a := by
  obtain ⟨a,ha⟩ := (FlexibleCloud.regularCSP C cloudEmbed).extend_complete padEmbed
    (CloudCopies.honest C x) (FlexibleCloud.regular_complete C cloudEmbed x hx)
  exact ⟨a,PortCSP.blend_complete _ _ a ha (PortCSP.always_complete _ a)⟩

omit [Fintype V] in
theorem sound (a : Node C → A) : C.rejection (decoded C padEmbed a) ≤
    (18*(ExpanderFamily.growth:ℝ)^2)*testRate ((csp C cloudEmbed padEmbed).Bad a) := by
  have hr := FlexibleCloud.regular_sound C cloudEmbed (a ∘ padEmbed)
  have hp := (FlexibleCloud.regularCSP C cloudEmbed).extend_failure_mass padEmbed a
  have hm := PortCSP.blend_failure (padded C cloudEmbed padEmbed) (PortCSP.always (strong C)) a
  rw [PortCSP.always_failure, mul_zero,add_zero] at hm
  change testRate ((csp C cloudEmbed padEmbed).Bad a)=testRate ((padded C cloudEmbed padEmbed).Bad a)/3 at hm
  change (Fintype.card (Node C):ℝ)*testRate ((padded C cloudEmbed padEmbed).Bad a)=_ at hp
  have hs : (Fintype.card (Node C):ℝ) ≤
      (ExpanderFamily.growth:ℝ)*Fintype.card (CloudCopies.Node C) := by
    exact_mod_cast node_relative_upper C
  have hn := testRate_nonneg ((padded C cloudEmbed padEmbed).Bad a)
  have hv : 0 < (Fintype.card (CloudCopies.Node C):ℝ) := by positivity
  have hl : testRate ((FlexibleCloud.regularCSP C cloudEmbed).Bad (a ∘ padEmbed)) ≤
      (ExpanderFamily.growth:ℝ)*testRate ((padded C cloudEmbed padEmbed).Bad a) := by
    apply (mul_le_mul_iff_right₀ hv).mp
    nlinarith only [hp,mul_le_mul_of_nonneg_right hs hn]
  change C.rejection (CloudCopies.decoded C (a ∘ padEmbed)) ≤ _
  have hg : 0 ≤ (ExpanderFamily.growth:ℝ) := Nat.cast_nonneg _
  nlinarith only [hr,mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num : (0:ℝ)≤6) hg),hm]

end FlexibleRegularization
end MetricKMedian.PCP

end Inline_PCPFlexibleRegularization

end OAI
