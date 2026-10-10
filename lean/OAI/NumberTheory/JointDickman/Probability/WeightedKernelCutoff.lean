import OAI.NumberTheory.JointDickman.Probability.IndependentKernelSplit

namespace OAI

/-! # Removing a bounded weight only discards the low-exclusive union -/

namespace JointDickman

open scoped BigOperators

section
variable {C E A : Type*} [Fintype C] [Fintype E] [DecidableEq A]

noncomputable def weightedDiscardedMass (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ) (a b : A) : ℝ :=
  independentPairMass w v cell a b -
    independentPairMass w (fun e => v e * weight e) cell a b

theorem weightedDiscardedMass_eq (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ) (a b : A) :
    weightedDiscardedMass w v cell weight a b =
      ∑ c, ∑ e₁, ∑ e₂, if cell c e₁ = some a ∧ cell c e₂ = some b then
        w c * v e₁ * v e₂ * (1 - weight e₁ * weight e₂) else 0 := by
  unfold weightedDiscardedMass
  simp only [independentPairMass_eq_triple, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e₁ _
  apply Finset.sum_congr rfl
  intro e₂ _
  split_ifs <;> ring

theorem weightedDiscardedMass_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e)
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1) (a b : A) :
    0 ≤ weightedDiscardedMass w v cell weight a b := by
  rw [weightedDiscardedMass_eq]
  apply Finset.sum_nonneg
  intro c _
  apply Finset.sum_nonneg
  intro e₁ _
  apply Finset.sum_nonneg
  intro e₂ _
  split_ifs
  · have hp : weight e₁ * weight e₂ ≤ 1 := by
      nlinarith [(hweight e₁).1, (hweight e₁).2, (hweight e₂).1, (hweight e₂).2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw c) (hv e₁)) (hv e₂)) (sub_nonneg.mpr hp)
  · exact le_rfl

theorem weightedDiscardedMass_le_lowUnion (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ)
    (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e)
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1)
    (hhigh : ∀ e, ¬low e → weight e = 1) (a b : A) :
    weightedDiscardedMass w v cell weight a b ≤ lowUnionExclusiveMass w v cell low a b := by
  rw [weightedDiscardedMass_eq]
  unfold lowUnionExclusiveMass
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro e₁ _
  apply Finset.sum_le_sum
  intro e₂ _
  by_cases hc : cell c e₁ = some a ∧ cell c e₂ = some b
  · simp only [hc, and_true, ↓reduceIte]
    by_cases hl : low e₁ ∨ low e₂
    · rw [ite_eq_left hl]
      have hp : 0 ≤ weight e₁ * weight e₂ := mul_nonneg (hweight e₁).1 (hweight e₂).1
      have hm := mul_nonneg (mul_nonneg (hw c) (hv e₁)) (hv e₂)
      nlinarith
    · rw [ite_eq_right hl]
      have hl' := not_or.mp hl
      rw [hhigh e₁ hl'.1, hhigh e₂ hl'.2]
      simp
  · have hc' : ¬((low e₁ ∨ low e₂) ∧ cell c e₁ = some a ∧ cell c e₂ = some b) := by tauto
    rw [ite_eq_right hc, ite_eq_right hc']

noncomputable def weightedDiscardedKernel (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ) (m : ℝ) (a b : A) : ℝ :=
  weightedDiscardedMass w v cell weight a b / (m * m)

theorem weightedDiscardedKernel_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e)
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1) {m : ℝ} (hm : 0 ≤ m) (a b : A) :
    0 ≤ weightedDiscardedKernel w v cell weight m a b :=
  div_nonneg (weightedDiscardedMass_nonneg w v cell weight hw hv hweight a b) (mul_nonneg hm hm)

theorem weightedDiscardedKernel_le_lowUnion (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ)
    (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e)
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1)
    (hhigh : ∀ e, ¬low e → weight e = 1) {m : ℝ} (hm : 0 ≤ m) (a b : A) :
    weightedDiscardedKernel w v cell weight m a b ≤
      lowUnionExclusiveKernel w v cell low (fun _ => m) a b :=
  div_le_div_of_nonneg_right (weightedDiscardedMass_le_lowUnion w v cell weight low hw hv
    hweight hhigh a b) (mul_nonneg hm hm)

end
end JointDickman

end OAI
