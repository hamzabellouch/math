import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweredAlphabet
import OAI.Combinatorics.KMedian.Amplification.PoweringBound
import OAI.Combinatorics.KMedian.Amplification.PoweringConstruction
import OAI.Combinatorics.KMedian.PCP.GlobalRegularization

namespace OAI

section Inline_PCPAmplifier

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier
abbrev Label := IncidenceReduction.Label
abbrev Degree := GlobalRegularization.Degree
def loss : ℕ := 18*ExpanderFamily.growth^2
def capLoss : ℕ := 384*576*16^4
def steps : ℕ := 2*capLoss*loss
def radius : ℕ := 2*steps+2
abbrev Bits := Advice.BitIndex Degree (Fin 4) radius
noncomputable instance bitsFintype : Fintype Bits := inferInstance
noncomputable instance bitsDecidableEq : DecidableEq Bits := Classical.decEq _
noncomputable instance edgeSampleFintype : Fintype (AlphabetReduction.EdgeSample Bits) := inferInstance

lemma loss_cast : (loss:ℝ)=18*(ExpanderFamily.growth:ℝ)^2 := by
  simp only [loss,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]

theorem loss_pos : 0 < loss := by
  have hg := ExpanderFamily.growth_gt_one
  unfold loss
  positivity

theorem capLoss_pos : 0 < capLoss := by norm_num [capLoss]
theorem steps_pos : 0 < steps := by
  unfold steps
  exact Nat.mul_pos (Nat.mul_pos (by omega) capLoss_pos) loss_pos

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
abbrev Node := GlobalRegularization.Node C
abbrev Edge := PortCSP.PowerEdge (G := GlobalRegularization.graph C) steps radius
noncomputable instance nodeFintype : Fintype (Node C) := inferInstance
noncomputable instance edgeFintype : Fintype (Edge C) := inferInstance
noncomputable def powered : BinaryCSP (Node C) (Edge C) (Advice Degree Label radius) := (GlobalRegularization.csp C).powered (cap := radius) steps
noncomputable def bits : BinaryCSP (Node C) (Edge C) (BitVector Bits) :=
  (powered C).mapLabels (Advice.bitsEquiv Degree (Fin 4) radius)
abbrev NewNode := AlphabetReduction.Position (bits C) ⊕ AlphabetReduction.Test (E := Edge C) (K := Bits)
abbrev NewEdge := AlphabetReduction.Test (E := Edge C) (K := Bits) × Fin 4
noncomputable instance newNodeFintype : Fintype (NewNode C) := by classical exact inferInstance
noncomputable instance newEdgeFintype : Fintype (NewEdge C) := inferInstance
noncomputable def result : BinaryCSP (NewNode C) (NewEdge C) Label := AlphabetReduction.binary (bits C)

noncomputable def poweredAssignment (a : NewNode C → Label) : Node C → Advice Degree Label radius :=
  (Advice.bitsEquiv Degree (Fin 4) radius).symm ∘
    AlphabetReduction.decoded (bits C) (IncidenceReduction.decoded a)
noncomputable def decoded (a : NewNode C → Label) : V → Label :=
  GlobalRegularization.decoded C ((GlobalRegularization.graph C).plurality (poweredAssignment C a) steps steps)

omit [Fintype V] in
theorem complete (x : V → Label) (hx : C.Satisfies x) : ∃ a, (result C).Satisfies a := by
  obtain ⟨b,hb⟩ := GlobalRegularization.complete C x hx
  exact (GlobalRegularization.csp C).powered_reduced_complete steps radius b hb

omit [Fintype V] in
theorem sound (a : NewNode C → Label) :
    min (2*C.rejection (decoded C a)) (1/(capLoss:ℝ)) ≤ (result C).rejection a := by
  have hp := (GlobalRegularization.csp C).powered_amplification
    (GlobalRegularization.contracts C) steps (Nat.one_le_iff_ne_zero.mpr steps_pos.ne')
    (poweredAssignment C a)
  have hg := GlobalRegularization.sound C
    ((GlobalRegularization.graph C).plurality (poweredAssignment C a) steps steps)
  have hb := AlphabetReduction.binary_sound (bits C) a
  have hm := (powered C).mapLabels_rejection (Advice.bitsEquiv Degree (Fin 4) radius)
    (AlphabetReduction.decoded (bits C) (IncidenceReduction.decoded a))
  change (bits C).rejection _=(powered C).rejection (poweredAssignment C a) at hm
  rw [hm] at hb
  rw [← loss_cast] at hg
  change C.rejection (decoded C a) ≤ (loss:ℝ)*_ at hg
  change (powered C).rejection (poweredAssignment C a)/384 ≤ (result C).rejection a at hb
  have hcard : Fintype.card Label=16 := by simp [Label,IncidenceReduction.Label,BitVector,Bit]
  rw [hcard] at hp
  change min ((steps:ℝ)*_) 1 ≤ 576*(16:ℝ)^4*(powered C).rejection (poweredAssignment C a) at hp
  have hcoef : (steps:ℝ)=2*(capLoss:ℝ)*(loss:ℝ) := by simp only [steps,Nat.cast_mul,Nat.cast_ofNat]
  have hc : 0 < (capLoss:ℝ) := Nat.cast_pos.mpr capLoss_pos
  have hl : 0 < (loss:ℝ) := Nat.cast_pos.mpr loss_pos
  have hmono : min (2*(capLoss:ℝ)*C.rejection (decoded C a)) 1 ≤
      min ((steps:ℝ)*testRate ((GlobalRegularization.csp C).Bad
        ((GlobalRegularization.graph C).plurality (poweredAssignment C a) steps steps))) 1 := by
    apply min_le_min_right
    rw [hcoef]
    nlinarith only [mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*(capLoss:ℝ) by positivity)]
  have hfin : min (2*(capLoss:ℝ)*C.rejection (decoded C a)) 1 ≤
      (capLoss:ℝ)*(result C).rejection a := by
    exact (hmono.trans hp).trans (by
      have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤384*576*16^4 by positivity)
      norm_num only [Nat.cast_ofNat,capLoss] at hh ⊢
      nlinarith only [hh])
  apply (mul_le_mul_iff_right₀ hc).mp
  rw [mul_min_of_nonneg _ _ hc.le]
  have he : (capLoss:ℝ)*(1/(capLoss:ℝ))=1 := by field_simp
  rw [he]
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hfin

end Amplifier
end MetricKMedian.PCP

end Inline_PCPAmplifier

end OAI
