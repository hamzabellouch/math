import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseIndependent
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseReferenceEvent

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryBulkFrequencyTransport HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryPairedFrequencyAverage

def independentReferenceIndicator (K : ℕ) {l : ℕ} (g g' h h' : History l)
    (z : ZMod ((pairedFrequencyProduct g g')^(K+2)) ×
      ZMod ((pairedFrequencyProduct g g')^(K+2))) : ℂ :=
  let R := pairedFrequencyProduct g g'
  let gF := fun s (hs : s∈g.frequencies) =>
    FrequencyPrecision.frequency_dvd_product (List.mem_append_left g'.frequencies hs)
  let gF' := fun s (hs : s∈g'.frequencies) =>
    FrequencyPrecision.frequency_dvd_product (List.mem_append_right g.frequencies hs)
  leafIndicator K R (frequencyScheduleAux R g g gF gF) (fixedFactorSchedule g g) g g []
    (l,initialResidueGiants K R z,initialResidueGiants K R z) (frequencyLeaves (R^(K+2)) h) *
  leafIndicator K R (frequencyScheduleAux R g' g' gF' gF') (fixedFactorSchedule g' g') g' g' []
    (l,initialResidueGiants K R z,initialResidueGiants K R z) (frequencyLeaves (R^(K+2)) h')

private theorem guardIndicator_interleave (A B C D : Prop) :
    guardIndicator ((A∧B)∧(C∧D)) = guardIndicator (A∧C)*guardIndicator (B∧D) := by
  rw [←guardIndicator_and]
  apply congrArg guardIndicator
  exact propext (by tauto)

theorem single_indicator_eq_reference (K R : ℕ) {l : ℕ} {h g : History l}
    (ha : SameFrequencyData h g)
    (hF : ∀s∈h.frequencies,s.natAbs∣R) (gF : ∀s∈g.frequencies,s.natAbs∣R)
    (z : ZMod (R^(K+2)) × ZMod (R^(K+2))) :
    guardIndicator (singleFiniteFrequencyUnits K R h hF z ∧ singleFiniteLeafAdmissible K R h hF z) =
      leafIndicator K R (frequencyScheduleAux R g g gF gF) (fixedFactorSchedule g g) g g []
        (l,initialResidueGiants K R z,initialResidueGiants K R z)
        (frequencyLeaves (R^(K+2)) h) := by
  change leafIndicator K R (frequencyScheduleAux R h h hF hF) (fixedFactorSchedule h h) h h [] _ _ = _
  rw [frequencyScheduleAux_eq R ha ha hF gF hF gF, fixedFactorSchedule_eq ha ha]
  exact leafIndicator_eq K R _ _ ha ha _ _ _

theorem independentIndicator_eq_aux (K R : ℕ) {l : ℕ} (h h' : History l)
    (hR : pairedFrequencyProduct h h'=R)
    (hF : ∀s∈h.frequencies,s.natAbs∣R) (hF' : ∀s∈h'.frequencies,s.natAbs∣R)
    (z : ZMod (R^(K+2)) × ZMod (R^(K+2))) :
    independentFrequencyResidueIndicator K h h' (residuePairTransport K hR z) =
      guardIndicator (singleFiniteFrequencyUnits K R h hF z ∧ singleFiniteLeafAdmissible K R h hF z) *
      guardIndicator (singleFiniteFrequencyUnits K R h' hF' z ∧ singleFiniteLeafAdmissible K R h' hF' z) := by
  subst R
  exact guardIndicator_interleave _ _ _ _

theorem independentIndicator_eq_reference {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g') (K : ℕ)
    (z : ZMod ((pairedFrequencyProduct g g')^(K+2)) ×
      ZMod ((pairedFrequencyProduct g g')^(K+2))) :
    independentFrequencyResidueIndicator K h h' (residuePairTransport K (pairedFrequencyProduct_eq ha hb) z) =
      independentReferenceIndicator K g g' h h' z := by
  have hF : ∀s∈h.frequencies,s.natAbs∣pairedFrequencyProduct g g' := by
    intro s hs
    rw [ha.frequencies_eq] at hs
    exact FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs)
  have hF' : ∀s∈h'.frequencies,s.natAbs∣pairedFrequencyProduct g g' := by
    intro s hs
    rw [hb.frequencies_eq] at hs
    exact FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs)
  rw [independentIndicator_eq_aux K _ h h' (pairedFrequencyProduct_eq ha hb) hF hF' z]
  exact congrArg₂ (·*·) (single_indicator_eq_reference K _ ha hF _ z)
    (single_indicator_eq_reference K _ hb hF' _ z)

theorem independentIndicator_eq_reference_intCast {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g') (K : ℕ) (Xp Xm : ℤ) :
    independentFrequencyResidueIndicator K h h' (Xp,Xm) =
      independentReferenceIndicator K g g' h h' (Xp,Xm) := by
  have he := independentIndicator_eq_reference ha hb K
    ((Xp:ZMod ((pairedFrequencyProduct g g')^(K+2))),
      (Xm:ZMod ((pairedFrequencyProduct g g')^(K+2))))
  erw [residuePairTransport_intCast] at he
  exact he

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
