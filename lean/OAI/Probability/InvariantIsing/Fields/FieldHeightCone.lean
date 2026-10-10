import OAI.Probability.InvariantIsing.Fields.FieldHeightJoint

namespace OAI

/-! The strict finite field-height cone and its original FieldStep
representatives. Positive increments give every height and order constraint. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def fieldStrictHeightCone (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {r | ∀ j, 0 < fieldHeightIncrement r j}

lemma continuous_fieldHeightIncrement {n : ℕ} (j : Fin (n + 1)) :
    Continuous (fun r : Fin (n + 1) → ℝ => fieldHeightIncrement r j) := by
  unfold fieldHeightIncrement
  split_ifs <;> fun_prop

lemma isOpen_fieldStrictHeightCone (n : ℕ) : IsOpen (fieldStrictHeightCone n) := by
  simpa only [fieldStrictHeightCone, ofPred_forall] using
    isOpen_iInter_of_finite (fun j : Fin (n + 1) =>
      isOpen_lt continuous_const (continuous_fieldHeightIncrement j))

lemma fieldHeightIncrement_succ {n : ℕ} (r : Fin (n + 1) → ℝ) (j : Fin n) :
    fieldHeightIncrement r j.succ = r j.succ - r j.castSucc := by
  unfold fieldHeightIncrement
  simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
    Nat.add_sub_cancel]
  rfl

lemma fieldStrictHeightCone_strictMono {n : ℕ} {r : Fin (n + 1) → ℝ}
    (hr : r ∈ fieldStrictHeightCone n) : StrictMono r := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  have h := hr j.succ
  rw [fieldHeightIncrement_succ] at h
  linarith

lemma fieldStrictHeightCone_nonneg {n : ℕ} {r : Fin (n + 1) → ℝ}
    (hr : r ∈ fieldStrictHeightCone n) (j : Fin (n + 1)) : 0 ≤ r j := by
  have h0 : 0 < r 0 := by simpa [fieldHeightIncrement] using hr 0
  exact h0.le.trans ((fieldStrictHeightCone_strictMono hr).monotone (Fin.zero_le j))

lemma convex_fieldStrictHeightCone (n : ℕ) : Convex ℝ (fieldStrictHeightCone n) := by
  intro r hr s hs a b ha hb hab j
  have he : fieldHeightIncrement (a • r + b • s) j =
      a * fieldHeightIncrement r j + b * fieldHeightIncrement s j := by
    unfold fieldHeightIncrement
    split_ifs <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [he]
  have hjr := hr j
  have hjs := hs j
  by_cases hzero : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [hzero, hb1] using hjs
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm hzero)) hjr)
      (mul_nonneg hb hjs.le)

def fieldStepOfStrictHeights (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) : FieldStep :=
  fieldWithHeights h r (fieldStrictHeightCone_nonneg hr) (fieldStrictHeightCone_strictMono hr).monotone

lemma fieldStepOfStrictHeights_strict (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (j : Fin (h.depth + 1)) :
    0 < (fieldIncrement (fieldStepOfStrictHeights h r hr) j).2 := hr j

lemma fieldHeightJointValue_strict (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (z : ℝ) :
    fieldHeightJointValue h r z = fieldValue (fieldStepOfStrictHeights h r hr) z :=
  fieldHeightJointValue_eq_fieldValue h r (fieldStrictHeightCone_nonneg hr)
    (fieldStrictHeightCone_strictMono hr).monotone z

end InvariantIsing

end

end OAI
