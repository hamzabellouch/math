import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverage

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Conclusion Characters BinaryExposure FrequencyExposure FrequencyTreeSum
open HistoryFrequencyResidues HistoryPairedFrequencyAverageHaar PairedFrequencyActualBudget

theorem bulk_ring_unit_giant_average_le {ε : ℝ} {C : NNReal}
    (hcount : LeafCountConstant ε C) (K R : ℕ) [NeZero R]
    (d : List Bool → Data R) (f : List Bool → FixedFactors × FixedFactors)
    {l : ℕ} (h h' : History l) (m : ℕ) (hm : 0 < m) :
    avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
      avg (fun z : ZMod (R^(K+2)) × (ZMod (R^(K+2)))ˣ =>
        ‖leafIndicator K R d f h h' []
          (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
          (bulkLeaves m l x)‖)) ≤
      ((FrequencyExposure.budget C ε (fun q => Template.ambientData K R (d q)) l []).value:ℝ) := by
  rw [avg_comm]
  exact leafIndicator_giant_bulk_average_le hcount K R d f h h' []
    (fun z : ZMod (R^(K+2)) × (ZMod (R^(K+2)))ˣ =>
      (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))) m hm

def canonicalRingUnitBulkAverage (K : ℕ) {l : ℕ} (h h' : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (hs' : h'.Supported V outside) (m : ℕ) : ℝ :=
  let R := pairedFrequencyProduct h h'
  letI : NeZero R := ⟨pairedFrequencyProduct_ne_zero hs hs'⟩
  avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
    avg (fun z : ZMod (R^(K+2)) × (ZMod (R^(K+2)))ˣ =>
      ‖leafIndicator K R (frequencySchedule h h') (fixedFactorSchedule h h') h h' []
        (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
        (bulkLeaves m l x)‖))

theorem canonicalRingUnitBulkAverage_le_weight {ε : ℝ} {C : NNReal}
    (hcount : LeafCountConstant ε C) (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (K : ℕ) {l : ℕ} (h h' : History l) {outside : List ℕ}
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : h'.Supported (frequencyBound Bs BD Bz k L) outside) (m : ℕ) (hm : 0 < m) :
    canonicalRingUnitBulkAverage K h h' hs hs' m ≤
      weight (pairedRanges Bs BD Bz k L l) (PairedFrequencyTreeSum.factor (C:ℝ) ε)
        (supportedHistoryAssignment Bs BD Bz k L h h' hs hs') := by
  let : NeZero (pairedFrequencyProduct h h') := ⟨pairedFrequencyProduct_ne_zero hs hs'⟩
  exact (bulk_ring_unit_giant_average_le hcount K (pairedFrequencyProduct h h')
    (frequencySchedule h h') (fixedFactorSchedule h h') h h' m hm).trans_eq
      (supported_history_budget_eq_weight Bs BD Bz k L K C ε h h' hs hs')

theorem sum_supported_ringUnit_average_le_total {ε : ℝ} {C : NNReal}
    (hcount : LeafCountConstant ε C) (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (K l m : ℕ) (hm : 0 < m) {ι : Type} [Fintype ι]
    (h h' : ι → History l) (outside : List ℕ)
    (hs : ∀i,(h i).Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : ∀i,(h' i).Supported (frequencyBound Bs BD Bz k L) outside)
    (hinj : Function.Injective (fun i =>
      supportedHistoryAssignment Bs BD Bz k L (h i) (h' i) (hs i) (hs' i))) :
    (∑i,canonicalRingUnitBulkAverage K (h i) (h' i) (hs i) (hs' i) m) ≤
      total (pairedRanges Bs BD Bz k L l) (PairedFrequencyTreeSum.factor (C:ℝ) ε) l [] := by
  classical
  apply Finset.sum_le_sum_of_injOn
    (fun i => supportedHistoryAssignment Bs BD Bz k L (h i) (h' i) (hs i) (hs' i))
    hinj.injOn (Finset.subset_univ _)
  · intro i _
    exact canonicalRingUnitBulkAverage_le_weight hcount Bs BD Bz k L K (h i) (h' i)
      (hs i) (hs' i) m hm
  · intro x _ _
    exact paired_weight_nonneg _ C ε x

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
