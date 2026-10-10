import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequencyBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIdentityFrequency
open Construction Characters FrequencyExposure BinaryExposure HistoryFrequencyResidues

theorem admissible_split (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (l : ℕ) (p : List Bool)
    (c : PairedContext R) (t : (ZMod (R^(K+2)))ˣ)
    (z : BinaryHaar.Splits (ZMod (R^(K+2)))ˣ l) :
    admissible (exposureConstraint K R d f)
      (update false (exposureStep K R d f false))
      (update true (exposureStep K R d f true)) l (p,c) t z ↔
    admissible (exposureConstraint K R (fun p=>leftData (d p)) (fun p=>leftFactors (f p)))
      (update false (exposureStep K R (fun p=>leftData (d p)) (fun p=>leftFactors (f p)) false))
      (update true (exposureStep K R (fun p=>leftData (d p)) (fun p=>leftFactors (f p)) true))
      l (p,leftContext c) t z ∧
    admissible (exposureConstraint K R (fun p=>rightData (d p)) (fun p=>rightFactors (f p)))
      (update false (exposureStep K R (fun p=>rightData (d p)) (fun p=>rightFactors (f p)) false))
      (update true (exposureStep K R (fun p=>rightData (d p)) (fun p=>rightFactors (f p)) true))
      l (p,rightContext c) t z := by
  induction l generalizing p c t with
  | zero => simp only [admissible,true_and]
  | succ l ih =>
    rcases z with ⟨x,zL,zR⟩
    simp only [admissible,update,exposureStep_left,exposureStep_right]
    rw [exposureConstraint_split,ih,ih]
    tauto

theorem leafAdmissible_split (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (l : ℕ) (p : List Bool)
    (c : PairedContext R) (z : BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l) :
    leafAdmissible (exposureConstraint K R d f)
      (update false (exposureStep K R d f false))
      (update true (exposureStep K R d f true)) l (p,c) z ↔
    leafAdmissible (exposureConstraint K R (fun p=>leftData (d p)) (fun p=>leftFactors (f p)))
      (update false (exposureStep K R (fun p=>leftData (d p)) (fun p=>leftFactors (f p)) false))
      (update true (exposureStep K R (fun p=>leftData (d p)) (fun p=>leftFactors (f p)) true))
      l (p,leftContext c) z ∧
    leafAdmissible (exposureConstraint K R (fun p=>rightData (d p)) (fun p=>rightFactors (f p)))
      (update false (exposureStep K R (fun p=>rightData (d p)) (fun p=>rightFactors (f p)) false))
      (update true (exposureStep K R (fun p=>rightData (d p)) (fun p=>rightFactors (f p)) true))
      l (p,rightContext c) z :=
  admissible_split K R d f l p c _ _

end Ostmann.Arithmetic.HistoryBulkIdentityFrequency

end

end OAI
