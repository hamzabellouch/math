import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageHaar

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Characters BinaryExposure FrequencyExposure
open HistoryFrequencyResidues HistorySignedResidueFactorization HistoryPairedFrequencyAverageHaar

theorem leafIndicator_bulk_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K R : ℕ) [NeZero R] (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (p : List Bool) (c : PairedContext R) (m : ℕ) (hm : 0 < m) :
    avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
      ‖leafIndicator K R d f h h' p c (bulkLeaves m l x)‖) ≤
      ((budget C ε (fun q => Template.ambientData K R (d q)) l p).value : ℝ) := by
  exact (bulkLeaves_avg (G:=(ZMod (R^(K+2)))ˣ) m l hm
    (fun z => ‖leafIndicator K R d f h h' p c z‖)).le.trans
      (leafIndicator_average_le hcount K R d f h h' p c)

theorem leafIndicator_giant_bulk_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K R : ℕ) [NeZero R] (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (p : List Bool) {α : Type} [Fintype α] [Nonempty α] (c : α → PairedContext R)
    (m : ℕ) (hm : 0 < m) :
    avg (fun z : α => avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
      ‖leafIndicator K R d f h h' p (c z) (bulkLeaves m l x)‖)) ≤
      ((budget C ε (fun q => Template.ambientData K R (d q)) l p).value : ℝ) := by
  calc
    _ = avg (fun z : α => avg (fun x : BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l =>
        ‖leafIndicator K R d f h h' p (c z) x‖)) := by
      apply congrArg avg
      funext z
      exact bulkLeaves_avg (G:=(ZMod (R^(K+2)))ˣ) m l hm
        (fun x => ‖leafIndicator K R d f h h' p (c z) x‖)
    _ ≤ _ := leafIndicator_giant_average_le hcount K R d f h h' p c

theorem leafIndicator_unit_giant_bulk_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K R : ℕ) [NeZero R] (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (m : ℕ) (hm : 0 < m) :
    avg (fun z : (ZMod (R^(K+2)))ˣ × (ZMod (R^(K+2)))ˣ =>
      avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
        ‖leafIndicator K R d f h h' []
          (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
          (bulkLeaves m l x)‖)) ≤
      ((budget C ε (fun q => Template.ambientData K R (d q)) l []).value : ℝ) := by
  exact leafIndicator_giant_bulk_average_le hcount K R d f h h' []
    (fun z : (ZMod (R^(K+2)))ˣ × (ZMod (R^(K+2)))ˣ =>
      (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))) m hm

theorem leafIndicator_mixed_giant_bulk_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K R : ℕ) [NeZero R] (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (m : ℕ) (hm : 0 < m) :
    avg (fun z : (ZMod (R^(K+2)))ˣ × ZMod (R^(K+2)) =>
      avg (fun x : (Fin (2^l) × Fin m) → (ZMod (R^(K+2)))ˣ =>
        ‖leafIndicator K R d f h h' []
          (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))
          (bulkLeaves m l x)‖)) ≤
      ((budget C ε (fun q => Template.ambientData K R (d q)) l []).value : ℝ) := by
  exact leafIndicator_giant_bulk_average_le hcount K R d f h h' []
    (fun z : (ZMod (R^(K+2)))ˣ × ZMod (R^(K+2)) =>
      (l,initialResidueGiants K R (z.1,z.2),initialResidueGiants K R (z.1,z.2))) m hm

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
