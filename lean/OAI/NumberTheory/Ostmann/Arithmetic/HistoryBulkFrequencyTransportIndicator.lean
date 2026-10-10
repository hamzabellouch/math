import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFrequencyTransportSchedules
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFrequencyTransport
open Construction HistoryFrequencyResidues HistorySignedResidueFactorization
open HistoryPairedFrequencyAverage Characters.FrequencyExposure

def residuePairTransport (K : ℕ) {R S : ℕ} (h : R=S)
    (z : ZMod (S^(K+2)) × ZMod (S^(K+2))) :
    ZMod (R^(K+2)) × ZMod (R^(K+2)) := h.symm ▸ z

theorem leafIndicator_eq (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g')
    (p : List Bool) (c : PairedContext R)
    (z : Characters.BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l) :
    leafIndicator K R d f h h' p c z=leafIndicator K R d f g g' p c z := by
  unfold leafIndicator
  apply congrArg guardIndicator
  exact propext (and_congr (knownPairFrequencyUnits_iff K R d f ha hb p c z) Iff.rfl)

theorem pairedIndicator_eq_aux (K R : ℕ) {l : ℕ} (h h' : History l)
    (hR : pairedFrequencyProduct h h'=R)
    (hF : ∀s∈h.frequencies,s.natAbs∣R) (hF' : ∀s∈h'.frequencies,s.natAbs∣R)
    (z : ZMod (R^(K+2)) × ZMod (R^(K+2))) :
    pairedFrequencyResidueIndicator K h h' (residuePairTransport K hR z)=
      leafIndicator K R (frequencyScheduleAux R h h' hF hF') (fixedFactorSchedule h h') h h' []
        (l,initialResidueGiants K R z,initialResidueGiants K R z)
        (frequencyLeaves (R^(K+2)) h) := by
  subst R
  rfl

theorem pairedIndicator_eq_reference {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g') (K : ℕ)
    (z : ZMod ((pairedFrequencyProduct g g')^(K+2)) ×
      ZMod ((pairedFrequencyProduct g g')^(K+2))) :
    pairedFrequencyResidueIndicator K h h' (residuePairTransport K (pairedFrequencyProduct_eq ha hb) z)=
      leafIndicator K (pairedFrequencyProduct g g') (frequencySchedule g g')
        (fixedFactorSchedule g g') g g' []
        (l,initialResidueGiants K (pairedFrequencyProduct g g') z,
          initialResidueGiants K (pairedFrequencyProduct g g') z)
        (frequencyLeaves ((pairedFrequencyProduct g g')^(K+2)) h) := by
  have hF : ∀s∈h.frequencies,s.natAbs∣pairedFrequencyProduct g g' := by
    intro s hs
    rw [ha.frequencies_eq] at hs
    exact FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs)
  have hF' : ∀s∈h'.frequencies,s.natAbs∣pairedFrequencyProduct g g' := by
    intro s hs
    rw [hb.frequencies_eq] at hs
    exact FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs)
  rw [pairedIndicator_eq_aux K _ h h' (pairedFrequencyProduct_eq ha hb) hF hF' z]
  have hd := frequencyScheduleAux_eq (pairedFrequencyProduct g g') ha hb hF
    (fun _ hs => FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs)) hF'
    (fun _ hs => FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs))
  rw [hd, fixedFactorSchedule_eq ha hb]
  exact leafIndicator_eq K _ _ _ ha hb _ _ _

end Ostmann.Arithmetic.HistoryBulkFrequencyTransport

end

end OAI
