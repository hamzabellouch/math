import Mathlib
import OAI.Combinatorics.KMedian.Amplification.Amplifier
import OAI.Combinatorics.KMedian.Amplification.FlexibleRegularization
import OAI.Combinatorics.KMedian.Amplification.PaddedPowered

namespace OAI

section Inline_PCPFlexibleAmplifier

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace FlexibleAmplifier
open Amplifier

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C)
abbrev Node := GlobalRegularization.Node C
abbrev Edge := PortCSP.PowerEdge (G := FlexibleRegularization.graph C cloudEmbed padEmbed) steps radius
noncomputable instance nodeFintype : Fintype (Node C) := inferInstance
noncomputable instance edgeFintype : Fintype (Edge C cloudEmbed padEmbed) := inferInstance
noncomputable def powered : BinaryCSP (Node C) (Edge C cloudEmbed padEmbed) (Advice Degree Label radius) := (FlexibleRegularization.csp C cloudEmbed padEmbed).powered (cap := radius) steps
noncomputable def bits : BinaryCSP (Node C) (Edge C cloudEmbed padEmbed) (BitVector Bits) :=
  (powered C cloudEmbed padEmbed).mapLabels (Advice.bitsEquiv Degree (Fin 4) radius)
abbrev NewNode := AlphabetReduction.PaddedNode (Node C) (Edge C cloudEmbed padEmbed) Bits
abbrev NewEdge := AlphabetReduction.Test (E := Edge C cloudEmbed padEmbed) (K := Bits) × Fin 4
noncomputable instance newNodeFintype : Fintype (NewNode C cloudEmbed padEmbed) := by classical exact inferInstance
noncomputable instance newEdgeFintype : Fintype (NewEdge C cloudEmbed padEmbed) := inferInstance
noncomputable def result : BinaryCSP (NewNode C cloudEmbed padEmbed) (NewEdge C cloudEmbed padEmbed) Label := AlphabetReduction.paddedBinary (bits C cloudEmbed padEmbed)

noncomputable def poweredAssignment (a : NewNode C cloudEmbed padEmbed → Label) : Node C → Advice Degree Label radius :=
  (Advice.bitsEquiv Degree (Fin 4) radius).symm ∘
    AlphabetReduction.decoded (bits C cloudEmbed padEmbed) (IncidenceReduction.decoded (a ∘ AlphabetReduction.nodeEmbed (bits C cloudEmbed padEmbed)))
noncomputable def decoded (a : NewNode C cloudEmbed padEmbed → Label) : V → Label :=
  FlexibleRegularization.decoded C padEmbed ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality (poweredAssignment C cloudEmbed padEmbed a) steps steps)

omit [Fintype V] [Nonempty E] in
theorem complete (x : V → Label) (hx : C.Satisfies x) : ∃ a, (result C cloudEmbed padEmbed).Satisfies a := by
  obtain ⟨b,hb⟩ := FlexibleRegularization.complete C cloudEmbed padEmbed x hx
  exact (FlexibleRegularization.csp C cloudEmbed padEmbed).powered_padded_complete steps radius b hb

omit [Fintype V] in
theorem sound (a : NewNode C cloudEmbed padEmbed → Label) :
    min (2*C.rejection (decoded C cloudEmbed padEmbed a)) (1/(capLoss:ℝ)) ≤ (result C cloudEmbed padEmbed).rejection a := by
  have hp := (FlexibleRegularization.csp C cloudEmbed padEmbed).powered_amplification
    (FlexibleRegularization.contracts C cloudEmbed padEmbed) steps (Nat.one_le_iff_ne_zero.mpr steps_pos.ne')
    (poweredAssignment C cloudEmbed padEmbed a)
  have hg := FlexibleRegularization.sound C cloudEmbed padEmbed
    ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality (poweredAssignment C cloudEmbed padEmbed a) steps steps)
  have hb := AlphabetReduction.padded_sound (bits C cloudEmbed padEmbed) a
  have hm := (powered C cloudEmbed padEmbed).mapLabels_rejection (Advice.bitsEquiv Degree (Fin 4) radius)
    (AlphabetReduction.decoded (bits C cloudEmbed padEmbed) (IncidenceReduction.decoded (a ∘ AlphabetReduction.nodeEmbed (bits C cloudEmbed padEmbed))))
  change (bits C cloudEmbed padEmbed).rejection _=(powered C cloudEmbed padEmbed).rejection (poweredAssignment C cloudEmbed padEmbed a) at hm
  rw [hm] at hb
  rw [← loss_cast] at hg
  change C.rejection (decoded C cloudEmbed padEmbed a) ≤ (loss:ℝ)*_ at hg
  change (powered C cloudEmbed padEmbed).rejection (poweredAssignment C cloudEmbed padEmbed a)/384 ≤ (result C cloudEmbed padEmbed).rejection a at hb
  have hcard : Fintype.card Label=16 := by simp [Label,IncidenceReduction.Label,BitVector,Bit]
  rw [hcard] at hp
  change min ((steps:ℝ)*_) 1 ≤ 576*(16:ℝ)^4*(powered C cloudEmbed padEmbed).rejection (poweredAssignment C cloudEmbed padEmbed a) at hp
  have hcoef : (steps:ℝ)=2*(capLoss:ℝ)*(loss:ℝ) := by simp only [steps,Nat.cast_mul,Nat.cast_ofNat]
  have hc : 0 < (capLoss:ℝ) := Nat.cast_pos.mpr capLoss_pos
  have hl : 0 < (loss:ℝ) := Nat.cast_pos.mpr loss_pos
  have hmono : min (2*(capLoss:ℝ)*C.rejection (decoded C cloudEmbed padEmbed a)) 1 ≤
      min ((steps:ℝ)*testRate ((FlexibleRegularization.csp C cloudEmbed padEmbed).Bad
        ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality (poweredAssignment C cloudEmbed padEmbed a) steps steps))) 1 := by
    apply min_le_min_right
    rw [hcoef]
    nlinarith only [mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*(capLoss:ℝ) by positivity)]
  have hfin : min (2*(capLoss:ℝ)*C.rejection (decoded C cloudEmbed padEmbed a)) 1 ≤
      (capLoss:ℝ)*(result C cloudEmbed padEmbed).rejection a := by
    exact (hmono.trans hp).trans (by
      have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤384*576*16^4 by positivity)
      norm_num only [Nat.cast_ofNat,capLoss] at hh ⊢
      nlinarith only [hh])
  apply (mul_le_mul_iff_right₀ hc).mp
  rw [mul_min_of_nonneg _ _ hc.le]
  have he : (capLoss:ℝ)*(1/(capLoss:ℝ))=1 := by field_simp
  rw [he]
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hfin

end FlexibleAmplifier
end MetricKMedian.PCP

end Inline_PCPFlexibleAmplifier

end OAI
