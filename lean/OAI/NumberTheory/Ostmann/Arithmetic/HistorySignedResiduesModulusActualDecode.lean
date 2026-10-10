import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCounts
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction Conclusion HistorySymbolicEncoding

theorem factorBound_decode (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (k N : ℕ) (B : ℝ)
    (hcount : ∀ j ≤ k, (Template.current seed j).length ≤ N)
    (hV : ∀ j ≤ k, (V j:ℝ) ≤ B)
    (hsource : ∀ origin, ∀ p : (sources origin).Sample,
      (sources origin).law.mass p ≠ 0 → ((p:ℕ):ℝ) ≤ B)
    (l : ℕ) (hlk : l ≤ k) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hroot : ∀ q ∈ a.small, sourceMass sources q ≠ 0)
    (hc : choicesMass sources seed V l c ≠ 0)
    (hfreq : |(a.frequency:ℝ)| ≤ B) :
    factorBound N B (decodeHistory sources seed V l a c) := by
  induction l generalizing a with
  | zero =>
    exact ⟨hfreq, (Template.matches_length ha).le.trans (hcount 0 hlk),
      fun q hq => sourceMass_value_le hsource (hroot q hq)⟩
  | succ l ih =>
    let H := decodeHistory sources seed V (l+1) a c
    let U := assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) c.2.2.1
    have hc' :
        (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mass c.2.2.1 *
        choicesMass sources seed V l c.2.2.2.1 * choicesMass sources seed V l c.2.2.2.2 ≠ 0 := hc
    have hUmass := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc').1).1
    have hleftmass := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc').1).2
    have hrightmass := (mul_ne_zero_iff.mp hc').2
    have hu : ∀ q ∈ U, sourceMass sources q ≠ 0 :=
      assignedSlots_source_mass_ne_zero sources _ c.2.2.1 hUmass
    have hchild := decoded_children_small_perm sources seed V l a c (Template.matches_length ha)
    have hmatches := decoded_children_match sources seed V l a c ha
    have hlmass : ∀ q ∈ (History.nodeLeft H).root.small, sourceMass sources q ≠ 0 := by
      intro q hq
      rcases List.mem_append.mp (hchild.1.mem_iff.mp hq) with hq | hq
      · exact hu q hq
      · exact hroot q (List.mem_of_mem_take hq)
    have hrmass : ∀ q ∈ (History.nodeRight H).root.small, sourceMass sources q ≠ 0 := by
      intro q hq
      rcases List.mem_append.mp (hchild.2.mem_iff.mp hq) with hq | hq
      · exact hu q hq
      · exact hroot q (List.mem_of_mem_drop hq)
    have hlk' : l ≤ k := by omega
    have child_freq (v : AllowedFrequency V l) : |(v.val:ℝ)| ≤ B := by
      have hv : |v.val| ≤ (V l:ℤ) := abs_le.mpr (Finset.mem_Icc.mp v.property)
      have hv' : |(v.val:ℝ)| ≤ (V l:ℝ) := by exact_mod_cast hv
      exact hv'.trans (hV l hlk')
    have hl := ih hlk' (History.nodeLeft H).root c.2.2.2.1 hmatches.1 hlmass hleftmass
      (by simpa only [H, decodeHistory, History.nodeLeft, decodeHistory_root] using child_freq c.1)
    have hr := ih hlk' (History.nodeRight H).root c.2.2.2.2 hmatches.2 hrmass hrightmass
      (by simpa only [H, decodeHistory, History.nodeRight, decodeHistory_root] using child_freq c.2.1)
    have hUlen : U.length ≤ N := by
      rw [show U.length = (Template.extracted (l+1) (Template.current seed l)).length from
        assignedSlots_length _ _ _]
      exact (List.length_filter_le _ _).trans (hcount l hlk')
    change |(a.frequency:ℝ)| ≤ B ∧ a.small.length ≤ N ∧ (∀ q ∈ a.small, (q.value:ℝ) ≤ B) ∧
      U.length ≤ N ∧ (∀ q ∈ U, (q.value:ℝ) ≤ B) ∧
      factorBound N B (History.nodeLeft H) ∧ factorBound N B (History.nodeRight H)
    refine ⟨hfreq, (Template.matches_length ha).le.trans (hcount (l+1) hlk),
      fun q hq => sourceMass_value_le hsource (hroot q hq), hUlen,
      fun q hq => sourceMass_value_le hsource (hu q hq), ?_, ?_⟩
    · simpa only [H, decodeHistory, History.nodeLeft, decodeHistory_root] using hl
    · simpa only [H, decodeHistory, History.nodeRight, decodeHistory_root] using hr

theorem actual_current_length_le (k : ℕ) (L : ℝ) {j : ℕ} (hj : j ≤ k) :
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) j).length ≤ actualFactorCount k L := by
  have hh := template_current_length_le (Template.initial (2*(bulkSize k L/2)) k) j
  rw [InitialCoordinatesTemplate.initial_length] at hh
  have hpow : 2^j ≤ (2^k:ℕ) := Nat.pow_le_pow_right (by omega) hj
  have hm : 2*(bulkSize k L/2) ≤ bulkSize k L := by omega
  have hseed : 2*(bulkSize k L/2)+6+4*k ≤ (6+4*k)*(bulkSize k L+1) := by nlinarith
  simpa only [actualFactorCount, Nat.mul_assoc] using hh.trans (Nat.mul_le_mul hpow hseed)

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
