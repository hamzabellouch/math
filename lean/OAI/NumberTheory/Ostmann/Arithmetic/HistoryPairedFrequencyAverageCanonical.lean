import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageOrder

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Characters BinaryExposure FrequencyExposure
open HistoryFrequencyResidues HistoryPairedFrequencyAverageHaar

def canonicalUnitBulkAverage (K : ℕ) {l : ℕ} (h h' : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (hs' : h'.Supported V outside) (m : ℕ) : ℝ :=
  let R := pairedFrequencyProduct h h'
  letI : NeZero R := ⟨pairedFrequencyProduct_ne_zero hs hs'⟩
  avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
    avg (fun z : (ZMod (R^(K+2)))ˣ × (ZMod (R^(K+2)))ˣ =>
      ‖leafIndicator K R (frequencySchedule h h') (fixedFactorSchedule h h') h h' []
        (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
        (bulkLeaves m l x)‖))

def canonicalMixedBulkAverage (K : ℕ) {l : ℕ} (h h' : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (hs' : h'.Supported V outside) (m : ℕ) : ℝ :=
  let R := pairedFrequencyProduct h h'
  letI : NeZero R := ⟨pairedFrequencyProduct_ne_zero hs hs'⟩
  avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
    avg (fun z : (ZMod (R^(K+2)))ˣ × ZMod (R^(K+2)) =>
      ‖leafIndicator K R (frequencySchedule h h') (fixedFactorSchedule h h') h h' []
        (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
        (bulkLeaves m l x)‖))

theorem canonicalUnitBulkAverage_le_budget {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside) (m : ℕ) (hm : 0 < m) :
    canonicalUnitBulkAverage K h h' hs hs' m ≤
      ((budget C ε (fun q => Template.ambientData K (pairedFrequencyProduct h h')
        (frequencySchedule h h' q)) l []).value:ℝ) := by
  let : NeZero (pairedFrequencyProduct h h') := ⟨pairedFrequencyProduct_ne_zero hs hs'⟩
  exact bulk_unit_giant_average_le hcount K (pairedFrequencyProduct h h')
    (frequencySchedule h h') (fixedFactorSchedule h h') h h' m hm

theorem canonicalMixedBulkAverage_le_budget {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside) (m : ℕ) (hm : 0 < m) :
    canonicalMixedBulkAverage K h h' hs hs' m ≤
      ((budget C ε (fun q => Template.ambientData K (pairedFrequencyProduct h h')
        (frequencySchedule h h' q)) l []).value:ℝ) := by
  let : NeZero (pairedFrequencyProduct h h') := ⟨pairedFrequencyProduct_ne_zero hs hs'⟩
  exact bulk_mixed_giant_average_le hcount K (pairedFrequencyProduct h h')
    (frequencySchedule h h') (fixedFactorSchedule h h') h h' m hm

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
