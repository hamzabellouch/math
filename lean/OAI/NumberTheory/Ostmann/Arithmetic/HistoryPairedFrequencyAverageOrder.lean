import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageBulk

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Characters BinaryExposure FrequencyExposure
open HistoryFrequencyResidues HistoryPairedFrequencyAverageHaar

theorem avg_comm {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    avg (fun x : α => avg (f x)) = avg (fun y : β => avg (fun x : α => f x y)) := by
  calc
    _ = avg (fun z : α×β => f z.1 z.2) := (avg_prod _).symm
    _ = avg (fun z : β×α => f z.2 z.1) :=
      avg_equiv (Equiv.prodComm α β) (fun z : β×α => f z.2 z.1)
    _ = _ := avg_prod _

theorem bulk_unit_giant_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K R : ℕ) [NeZero R] (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (m : ℕ) (hm : 0 < m) :
    avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
      avg (fun z : (ZMod (R^(K+2)))ˣ × (ZMod (R^(K+2)))ˣ =>
        ‖leafIndicator K R d f h h' []
          (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
          (bulkLeaves m l x)‖)) ≤
      ((budget C ε (fun q => Template.ambientData K R (d q)) l []).value : ℝ) := by
  rw [avg_comm]
  exact leafIndicator_unit_giant_bulk_average_le hcount K R d f h h' m hm

theorem bulk_mixed_giant_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K R : ℕ) [NeZero R] (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (m : ℕ) (hm : 0 < m) :
    avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
      avg (fun z : (ZMod (R^(K+2)))ˣ × ZMod (R^(K+2)) =>
        ‖leafIndicator K R d f h h' []
          (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
          (bulkLeaves m l x)‖)) ≤
      ((budget C ε (fun q => Template.ambientData K R (d q)) l []).value : ℝ) := by
  rw [avg_comm]
  exact leafIndicator_mixed_giant_bulk_average_le hcount K R d f h h' m hm

theorem exists_bulk_frequency_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : NNReal, 0 < C ∧ ∀ K R : ℕ, ∀ [NeZero R],
      ∀ d : List Bool → Data R, ∀ f : List Bool → FixedFactors × FixedFactors,
      ∀ l : ℕ, ∀ h h' : History l, ∀ m : ℕ, 0 < m →
      avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
        avg (fun z : (ZMod (R^(K+2)))ˣ × (ZMod (R^(K+2)))ˣ =>
          ‖leafIndicator K R d f h h' []
            (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
            (bulkLeaves m l x)‖)) ≤
        ((budget C ε (fun q => Template.ambientData K R (d q)) l []).value : ℝ) := by
  obtain ⟨C,hC,hcount⟩ := paired_frequency_leaf_count ε hε
  exact ⟨C,hC,fun K R _ d f l h h' m hm =>
    bulk_unit_giant_average_le hcount K R d f h h' m hm⟩

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
