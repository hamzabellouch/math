import Mathlib
import OAI.Combinatorics.KMedian.Amplification.FlexibleBound
import OAI.Combinatorics.KMedian.Amplification.FlexibleComplete
import OAI.Combinatorics.KMedian.Amplification.PowerTable
import OAI.Combinatorics.KMedian.Machines.AlphabetSpec
import OAI.Combinatorics.KMedian.Machines.RelabelTables
import OAI.Combinatorics.KMedian.Machines.TablePromises

namespace OAI

section Inline_PCPAmplifierProgram
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic CloudSpec
open scoped Classical

noncomputable def power (s : CSPTable Label) := PowerProgram.table steps radius s
noncomputable def bits (s : CSPTable Label) : CSPTable (BitVector Bits) :=
  CSPTable.relabel (Advice.bitsEquiv Degree (Fin 4) radius) (power s)
noncomputable def next (s : CSPTable Label) : CSPTable Label := AlphabetProgram.table Bits (bits s)
lemma poly_bits : Poly bits := (CSPTable.poly_relabel _).comp (PowerProgram.poly_table steps radius)
lemma poly_next : Poly next := (AlphabetProgram.poly_table Bits).comp poly_bits
variable (s : CSPTable Label) (h : s.WellFormed) [Nonempty (Fin s.2.length)]
noncomputable def bitsRep : (bits s).Represents
    (FlexibleAmplifier.bits (C s h) (CloudOrder.cloudEmbed (C s h) (EO s)) (padding s h)) :=
  (PowerProgram.represents s h steps radius).relabel (Advice.bitsEquiv Degree (Fin 4) radius)
include h in
lemma bits_wellFormed : (bits s).WellFormed := (bitsRep s h).wellFormed
noncomputable def nextRep : (next s).Represents (AlphabetReduction.paddedBinary
    ((bits s).csp (bits_wellFormed s h))) := AlphabetProgram.represents Bits (bits s) (bits_wellFormed s h)
include h in
lemma next_wellFormed : (next s).WellFormed := by
  let : Nonempty (Fin (bits s).2.length) := Fin.pos_iff_nonempty.mp (bits_wellFormed s h).1
  exact (nextRep s h).wellFormed
lemma complete (hc : ∃ a, (s.csp h).Satisfies a) :
    ∃ a, ((next s).csp (next_wellFormed s h)).Satisfies a := by
  obtain ⟨a,ha⟩ := hc
  have hbb := FlexibleAmplifier.bits_complete (C s h)
    (CloudOrder.cloudEmbed (C s h) (EO s)) (padding s h) a ha
  obtain ⟨c,hc⟩ := (bitsRep s h).satisfies (bits_wellFormed s h) |>.mpr hbb
  obtain ⟨d,hd⟩ := AlphabetReduction.padded_complete ((bits s).csp (bits_wellFormed s h)) c hc
  exact (nextRep s h).satisfies (next_wellFormed s h) |>.mpr ⟨d,hd⟩
lemma gap (δ : ℝ) (hg : ∀ a, δ≤(s.csp h).rejection a) :
    ∀ a, min (2*δ) (1/(capLoss:ℝ)) ≤ ((next s).csp (next_wellFormed s h)).rejection a := by
  intro a
  let a' := a ∘ (nextRep s h).vertex
  let B := (bits s).csp (bits_wellFormed s h)
  let b := AlphabetReduction.decoded B (IncidenceReduction.decoded (a' ∘ AlphabetReduction.nodeEmbed B))
  have hb := AlphabetReduction.padded_sound B a'
  change B.rejection b/384≤_ at hb
  have hr := (nextRep s h).rejection (next_wellFormed s h) a
  change _=(AlphabetReduction.paddedBinary B).rejection a' at hr
  rw [← hr] at hb
  have hm := (bitsRep s h).rejection (bits_wellFormed s h) b
  have he := (FlexibleAmplifier.powered (C s h) (CloudOrder.cloudEmbed (C s h) (EO s))
    (padding s h)).mapLabels_rejection (Advice.bitsEquiv Degree (Fin 4) radius) (b ∘ (bitsRep s h).vertex)
  change B.rejection b=_ at hm
  have hhbits := hm.trans he
  rw [hhbits] at hb
  have hh := FlexibleAmplifier.sound_of_power_bound (C s h)
    (CloudOrder.cloudEmbed (C s h) (EO s)) (padding s h) _ _ hb
  exact (min_le_min_right _ (mul_le_mul_of_nonneg_left (hg _) (by norm_num))).trans hh
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierProgram

end OAI
