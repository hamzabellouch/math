import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumFrequency

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIdentityFrequency
open Construction Characters FrequencyExposure BinaryExposure HistoryFrequencyResidues

def leftData {R : ℕ} (d : Data R) : Data R :=
  ⟨d.s,d.s,d.v,d.w,d.v,d.w,d.divides,d.divides⟩
def rightData {R : ℕ} (d : Data R) : Data R :=
  ⟨d.s',d.s',d.v',d.w',d.v',d.w',d.divides',d.divides'⟩
def leftFactors (f : FixedFactors × FixedFactors) := (f.1,f.1)
def rightFactors (f : FixedFactors × FixedFactors) := (f.2,f.2)
def leftContext {R : ℕ} (c : PairedContext R) : PairedContext R := (c.1,c.2.1,c.2.1)
def rightContext {R : ℕ} (c : PairedContext R) : PairedContext R := (c.1,c.2.2,c.2.2)

theorem exposureStep_left (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (b : Bool) (p : List Bool)
    (c : PairedContext R) (t x : (ZMod (R^(K+2)))ˣ) :
    exposureStep K R (fun p => leftData (d p)) (fun p => leftFactors (f p)) b p
      (leftContext c) t x = leftContext (exposureStep K R d f b p c t x) := by
  by_cases hj : c.1-1<K <;>
    simp [exposureStep,leftContext,leftData,leftFactors,hj]
  rfl

theorem exposureStep_right (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (b : Bool) (p : List Bool)
    (c : PairedContext R) (t x : (ZMod (R^(K+2)))ˣ) :
    exposureStep K R (fun p => rightData (d p)) (fun p => rightFactors (f p)) b p
      (rightContext c) t x = rightContext (exposureStep K R d f b p c t x) := by
  by_cases hj : c.1-1<K <;>
    simp [exposureStep,rightContext,rightData,rightFactors,hj]
  rfl

theorem exposureConstraint_split (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (j : ℕ) (p : List Bool)
    (c : PairedContext R) (t x : (ZMod (R^(K+2)))ˣ) :
    exposureConstraint K R d f j (p,c) t x ↔
      exposureConstraint K R (fun p => leftData (d p)) (fun p => leftFactors (f p))
        j (p,leftContext c) t x ∧
      exposureConstraint K R (fun p => rightData (d p)) (fun p => rightFactors (f p))
        j (p,rightContext c) t x := by
  simp only [exposureConstraint,constraint,exposureCoefficients,Template.ambientData,
    leftData,rightData,leftFactors,rightFactors,leftContext,rightContext]
  constructor
  · rintro ⟨hl,hr⟩
    exact ⟨⟨hl,hl⟩,hr,hr⟩
  · rintro ⟨hl,hr⟩
    exact ⟨hl.1,hr.1⟩

end Ostmann.Arithmetic.HistoryBulkIdentityFrequency

end

end OAI
