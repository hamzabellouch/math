import Mathlib
import OAI.Geometry.HyperbolicGroups.ExtensionConditioning
import OAI.Geometry.HyperbolicGroups.LeafFiber
import OAI.Geometry.HyperbolicGroups.Normalization

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

def branchDeviation (support : R → Finset F) (U : Finset F) (j : B) (a : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) : ℝ :=
  ∑ σ : F → A, if TableModel.IsMatch support w σ then
    |(extensionCount support U j (branchValues U σ) w : ℝ) - a| else 0

def leafDeviation (support : R → Finset F) (U : Finset F) (e : F) (a₀ : A) (b : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) : ℝ :=
  ∑ a : B ↪ A, |(leafCount support U e (leafValues U a a₀) w : ℝ) - b|

omit [DecidableEq R] in
lemma branchDeviation_nonneg (support : R → Finset F) (U : Finset F) (j : B) (a : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) : 0 ≤ branchDeviation support U j a w := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs <;> positivity

omit [DecidableEq R] in
lemma leafDeviation_nonneg (support : R → Finset F) (U : Finset F) (e : F) (a₀ : A) (b : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) : 0 ≤ leafDeviation (B := B) support U e a₀ b w := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Summing the conditional first-moment bounds costs the expected number of
master matches, *not* the number of all assignments without its match factor. -/
theorem expect_branchDeviation (support : R → Finset F) (U : Finset F) (j : B)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (ξ : Var (B := B) U → A)
    {r : ℝ} (hr : 0 ≤ r)
    (hv : ∀ σ : F → A,
      (TableModel.law support p hp).variance (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) ≤
        r * (TableModel.law support p hp).expect (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) ^ 2) :
    let μ := TableModel.law (A := A) support p hp
    let a := μ.expect (fun w => (extensionCount support U j ξ w : ℝ))
    μ.expect (branchDeviation support U j a) ≤
      ((Fintype.card (F → A) : ℝ) * ∏ r, p r) * Real.sqrt r * a := by
  dsimp only
  let μ := TableModel.law (A := A) support p hp
  let a := μ.expect (fun w => (extensionCount support U j ξ w : ℝ))
  change μ.expect (branchDeviation support U j a) ≤ _
  have hs (σ : F → A) : μ.expect (fun w => if TableModel.IsMatch support w σ then
      |(extensionCount support U j (branchValues U σ) w : ℝ) - a| else 0) ≤
        (∏ s, p s) * (Real.sqrt r * a) := by
    have hc := extension_conditioning support U j (branchValues (B := B) U σ) p hp (fun n => |(n : ℝ) - a|)
    simp only [branchValues_coord] at hc
    rw [show μ.expect (fun w => if TableModel.IsMatch support w σ then
      |(extensionCount support U j (branchValues U σ) w : ℝ) - a| else 0) =
      (∏ s, p s) * μ.expect (fun w => |(extensionCount support U j (branchValues U σ) w : ℝ) - a|) from hc]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => (hp s).1)
    have he : μ.expect (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) = a :=
      extension_expect_eq support U j _ ξ p hp
    have hh := μ.expect_abs_sub_le_relative (fun w => (extensionCount support U j (branchValues U σ) w : ℝ))
      hr (μ.expect_nonneg fun _ => Nat.cast_nonneg _) (hv σ)
    simpa only [he] using hh
  unfold branchDeviation
  rw [μ.expect_sum]
  calc
    _ ≤ ∑ _σ : F → A, (∏ s, p s) * (Real.sqrt r * a) := Finset.sum_le_sum fun σ _ => hs σ
    _ = _ := by simp [a,μ]; ring

/-- The corresponding unconditional L1 bound for ordered-distinct leaf lists. -/
theorem expect_leafDeviation (support : R → Finset F) (U : Finset F) (e : F)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (ξ : Var (B := B) U → A)
    (hξ : PinnedAssignments.PinFieldwise (field U) (leafPins U e) ξ) (a₀ : A)
    {r : ℝ} (hr : 0 ≤ r)
    (hv : ∀ a : B ↪ A,
      (TableModel.law support p hp).variance (fun w => (leafCount support U e (leafValues U a a₀) w : ℝ)) ≤
        r * (TableModel.law support p hp).expect (fun w => (leafCount support U e (leafValues U a a₀) w : ℝ)) ^ 2) :
    let μ := TableModel.law (A := A) support p hp
    let b := μ.expect (fun w => (leafCount support U e ξ w : ℝ))
    μ.expect (leafDeviation (B := B) support U e a₀ b) ≤
      (Fintype.card (B ↪ A) : ℝ) * Real.sqrt r * b := by
  dsimp only
  let μ := TableModel.law (A := A) support p hp
  let b := μ.expect (fun w => (leafCount support U e ξ w : ℝ))
  change μ.expect (leafDeviation support U e a₀ b) ≤ _
  unfold leafDeviation
  rw [μ.expect_sum]
  calc
    _ ≤ ∑ _a : B ↪ A, Real.sqrt r * b := by
      apply Finset.sum_le_sum
      intro a _
      have he : μ.expect (fun w => (leafCount support U e (leafValues U a a₀) w : ℝ)) = b :=
        leaf_expect_eq support U e _ ξ p hp (leaf_pin_fieldwise U e a a₀) hξ
      have hh := μ.expect_abs_sub_le_relative (fun w => (leafCount support U e (leafValues U a a₀) w : ℝ))
        hr (μ.expect_nonneg fun _ => Nat.cast_nonneg _) (hv a)
      simpa only [he] using hh
    _ = _ := by simp [b,μ]; ring

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
