import Mathlib
import OAI.Combinatorics.KMedian.Amplification.FlexibleAmplifier

namespace OAI

section Inline_PCPFlexibleBound
namespace MetricKMedian.PCP.FlexibleAmplifier
open Amplifier
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C)
omit [Fintype V] in
theorem sound_of_power_bound (a : Node C → Advice Degree Label radius) (r : ℝ)
    (hb : (powered C cloudEmbed padEmbed).rejection a /384 ≤ r) :
    min (2*C.rejection (FlexibleRegularization.decoded C padEmbed ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality a steps steps))) (1/(capLoss:ℝ)) ≤ r := by
  have hp := (FlexibleRegularization.csp C cloudEmbed padEmbed).powered_amplification
    (FlexibleRegularization.contracts C cloudEmbed padEmbed) steps (Nat.one_le_iff_ne_zero.mpr steps_pos.ne')
    a
  have hg := FlexibleRegularization.sound C cloudEmbed padEmbed
    ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality a steps steps)
  rw [← loss_cast] at hg
  change C.rejection (FlexibleRegularization.decoded C padEmbed ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality a steps steps)) ≤ (loss:ℝ)*_ at hg
  have hcard : Fintype.card Label=16 := by simp [Label,IncidenceReduction.Label,BitVector,Bit]
  rw [hcard] at hp
  change min ((steps:ℝ)*_) 1 ≤ 576*(16:ℝ)^4*(powered C cloudEmbed padEmbed).rejection a at hp
  have hcoef : (steps:ℝ)=2*(capLoss:ℝ)*(loss:ℝ) := by simp only [steps,Nat.cast_mul,Nat.cast_ofNat]
  have hc : 0 < (capLoss:ℝ) := Nat.cast_pos.mpr capLoss_pos
  have hl : 0 < (loss:ℝ) := Nat.cast_pos.mpr loss_pos
  have hmono : min (2*(capLoss:ℝ)*C.rejection (FlexibleRegularization.decoded C padEmbed ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality a steps steps))) 1 ≤
      min ((steps:ℝ)*testRate ((FlexibleRegularization.csp C cloudEmbed padEmbed).Bad
        ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality a steps steps))) 1 := by
    apply min_le_min_right
    rw [hcoef]
    nlinarith only [mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*(capLoss:ℝ) by positivity)]
  have hfin : min (2*(capLoss:ℝ)*C.rejection (FlexibleRegularization.decoded C padEmbed ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality a steps steps))) 1 ≤
      (capLoss:ℝ)*r := by
    exact (hmono.trans hp).trans (by
      have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤384*576*16^4 by positivity)
      norm_num only [Nat.cast_ofNat,capLoss] at hh ⊢
      nlinarith only [hh])
  apply (mul_le_mul_iff_right₀ hc).mp
  rw [mul_min_of_nonneg _ _ hc.le]
  have he : (capLoss:ℝ)*(1/(capLoss:ℝ))=1 := by field_simp
  rw [he]
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hfin

end MetricKMedian.PCP.FlexibleAmplifier

end Inline_PCPFlexibleBound

end OAI
