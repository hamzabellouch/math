import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFrequencyTransportBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextDefs

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFrequencyTransport
open Construction HistoryBulkProducts HistoryFrequencyResidues Characters.FrequencyExposure

theorem fixedFactorSchedule_eq {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g') :
    fixedFactorSchedule h h'=fixedFactorSchedule g g' := by
  induction h with
  | leaf a => cases g; cases h'; cases g'; rfl
  | node a p u hp hm left right il ir =>
    cases g with
    | node b q v bp bm leftg rightg =>
      cases h' with
      | node a' p' u' hp' hm' left' right' =>
        cases g' with
        | node b' q' v' bp' bm' leftg' rightg' =>
          simp only [SameFrequencyData] at ha hb
          simp only [fixedFactorSchedule, ha.2.1, ha.2.2.1, ha.2.2.2.1,
            hb.2.1, hb.2.2.1, hb.2.2.2.1,
            il ha.2.2.2.2.1 hb.2.2.2.2.1, ir ha.2.2.2.2.2 hb.2.2.2.2.2]

theorem frequencyScheduleAux_eq (R : ℕ) {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g')
    (hF : ∀s∈h.frequencies,s.natAbs∣R) (gF : ∀s∈g.frequencies,s.natAbs∣R)
    (hF' : ∀s∈h'.frequencies,s.natAbs∣R) (gF' : ∀s∈g'.frequencies,s.natAbs∣R) :
    frequencyScheduleAux R h h' hF hF'=frequencyScheduleAux R g g' gF gF' := by
  induction h with
  | leaf a =>
    cases g with
    | leaf b =>
      cases h' with
      | leaf a' =>
        cases g' with
        | leaf b' =>
          simp only [SameFrequencyData] at ha hb
          simp only [frequencyScheduleAux,actualNodeData,ha,hb]
  | node a p u hp hm left right il ir =>
    cases g with
    | node b q v bp bm leftg rightg =>
      cases h' with
      | node a' p' u' hp' hm' left' right' =>
        cases g' with
        | node b' q' v' bp' bm' leftg' rightg' =>
          have hl := ha.2.2.2.2.1.root_frequency_eq
          have hr := ha.2.2.2.2.2.root_frequency_eq
          have hl' := hb.2.2.2.2.1.root_frequency_eq
          have hr' := hb.2.2.2.2.2.root_frequency_eq
          simp only [SameFrequencyData] at ha hb
          simp only [frequencyScheduleAux]
          congr 1
          · simp only [actualNodeData,ha.1,hb.1,hl,hr,hl',hr']
          · exact il ha.2.2.2.2.1 hb.2.2.2.2.1 _ _ _ _
          · exact ir ha.2.2.2.2.2 hb.2.2.2.2.2 _ _ _ _

theorem knownPairFrequencyUnits_iff (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g')
    (p : List Bool) (c : PairedContext R)
    (z : Characters.BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l) :
    knownPairFrequencyUnits K R d f h h' p c z ↔
      knownPairFrequencyUnits K R d f g g' p c z := by
  induction h generalizing p c with
  | leaf a =>
    cases g; cases h'; cases g'
    simp only [knownPairFrequencyUnits,ha.frequencies_eq,hb.frequencies_eq]
  | node a q u hp hm left right il ir =>
    cases g with
    | node b q' v bp bm leftg rightg =>
      cases h' with
      | node a' r u' hp' hm' left' right' =>
        cases g' with
        | node b' r' v' bp' bm' leftg' rightg' =>
          simp only [knownPairFrequencyUnits,ha.frequencies_eq,hb.frequencies_eq,
            il ha.2.2.2.2.1 hb.2.2.2.2.1,ir ha.2.2.2.2.2 hb.2.2.2.2.2]

end Ostmann.Arithmetic.HistoryBulkFrequencyTransport

end

end OAI
