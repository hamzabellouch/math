import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlockDefs
import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyActualBudgetTotal

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Characters BinaryExposure FrequencyExposure
open HistoryFrequencyResidues HistorySignedResidueFactorization

def leafIndicator (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (p : List Bool) (c : PairedContext R)
    (z : BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l) : ℂ :=
  guardIndicator (knownPairFrequencyUnits K R d f h h' p c z ∧
    leafAdmissible (exposureConstraint K R d f)
      (update false (exposureStep K R d f false))
      (update true (exposureStep K R d f true)) l (p,c) z)

theorem pairedFrequencyResidueIndicator_eq_leafIndicator (K : ℕ) {l : ℕ}
    (h h' : History l)
    (z : ZMod ((pairedFrequencyProduct h h')^(K+2)) ×
      ZMod ((pairedFrequencyProduct h h')^(K+2))) :
    pairedFrequencyResidueIndicator K h h' z =
      leafIndicator K (pairedFrequencyProduct h h') (frequencySchedule h h')
        (fixedFactorSchedule h h') h h' []
        (l,initialResidueGiants K (pairedFrequencyProduct h h') z,
          initialResidueGiants K (pairedFrequencyProduct h h') z)
        (frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h) := rfl

theorem guarded_leaf_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (Q : ℕ) [NeZero Q] (H : Type)
    (d : List Bool → Data Q) (a : ∀p,Coefficients H (d p))
    (left right : List Bool → H → (ZMod Q)ˣ → (ZMod Q)ˣ → H)
    (l : ℕ) (p : List Bool) (h : H)
    (guard : BinaryHaar.Leaves (ZMod Q)ˣ l → Prop) :
    avg (fun z : BinaryHaar.Leaves (ZMod Q)ˣ l =>
      ‖guardIndicator (guard z ∧ leafAdmissible (constraint d a)
        (update false left) (update true right) l (p,h) z)‖) ≤
      ((budget C ε d l p).value : ℝ) := by
  classical
  calc
    _ ≤ avg (fun z : BinaryHaar.Leaves (ZMod Q)ˣ l =>
        if leafAdmissible (constraint d a) (update false left)
          (update true right) l (p,h) z then 1 else 0) := by
      apply avg_mono
      intro z
      by_cases he : leafAdmissible (constraint d a) (update false left)
        (update true right) l (p,h) z
      · by_cases hg : guard z <;> simp [guardIndicator,he,hg]
      · simp [guardIndicator,he]
    _ = _ := avg_indicator _
    _ ≤ _ := hcount Q H d a left right l p h

theorem leafIndicator_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K R : ℕ) [NeZero R] (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (p : List Bool) (c : PairedContext R) :
    avg (fun z : BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l =>
      ‖leafIndicator K R d f h h' p c z‖) ≤
      ((budget C ε (fun q => Template.ambientData K R (d q)) l p).value : ℝ) := by
  exact guarded_leaf_average_le hcount (R^(K+2)) (PairedContext R)
    (fun q => Template.ambientData K R (d q)) (exposureCoefficients K R d f)
    (exposureStep K R d f false) (exposureStep K R d f true) l p c
    (knownPairFrequencyUnits K R d f h h' p c)

theorem leafIndicator_giant_average_le {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (K R : ℕ) [NeZero R] (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h h' : History l)
    (p : List Bool) {α : Type} [Fintype α] [Nonempty α] (c : α → PairedContext R) :
    avg (fun x : α => avg (fun z : BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l =>
      ‖leafIndicator K R d f h h' p (c x) z‖)) ≤
      ((budget C ε (fun q => Template.ambientData K R (d q)) l p).value : ℝ) := by
  exact (avg_mono _ _ (fun x => leafIndicator_average_le hcount K R d f h h' p (c x))).trans_eq
    (avg_const _)

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
