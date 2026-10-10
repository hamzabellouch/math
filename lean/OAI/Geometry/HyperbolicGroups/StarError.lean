import Mathlib
import OAI.Geometry.HyperbolicGroups.StarMean

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α : Type*} [Fintype α]
lemma expect_div (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun a => f a / c) = μ.expect f / c := by
  simp only [expect, mul_div_assoc, Finset.sum_div]

lemma exists_lt_of_expect_lt (μ : FiniteLaw α) (f : α → ℝ) (t : ℝ)
    (h : μ.expect f < t) : ∃ a, f a < t := by
  by_contra! hn
  have hh := μ.expect_mono hn
  rw [μ.expect_const] at hh
  exact (not_lt_of_ge hh) h
end FiniteLaw

namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

/-- A single error statistic for the actual table, scaled by its nonrandom
expected star count. The leaf mean, not a fresh independent table, supplies the
normalizing-total estimate. -/
def normalizedError (support : R → Finset F) (U : Finset F) (e : F)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) : ℝ :=
  let μ := TableModel.law (A := A) support p hp
  ((∑ j : B, branchDeviation support U j
    (μ.expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ))) w) +
    leafDeviation (B := B) support U e a₀
      (μ.expect (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ))) w) /
    μ.expect (fun w => (starCount (B := B) support U w : ℝ))

lemma normalizedError_nonneg (support : R → Finset F) (U : Finset F) (e : F)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) :
    0 ≤ normalizedError support U e p hp a₀ b₀ w := by
  unfold normalizedError
  apply div_nonneg
  · exact add_nonneg (Finset.sum_nonneg fun j _ => branchDeviation_nonneg _ _ _ _ _)
      (leafDeviation_nonneg _ _ _ _ _ _)
  · exact FiniteLaw.expect_nonneg _ (fun _ => Nat.cast_nonneg _)

lemma expect_normalizedError_le (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (rE : B → ℝ) (rL : ℝ) (hrE : ∀ j, 0 ≤ rE j) (hrL : 0 ≤ rL)
    (hM : 0 < (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)))
    (hvE : ∀ j (σ : F → A),
      (TableModel.law (A := A) support p hp).variance (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) ≤
        rE j * (TableModel.law (A := A) support p hp).expect (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) ^ 2)
    (hvL : ∀ b : B ↪ A,
      (TableModel.law (A := A) support p hp).variance (fun w => (leafCount support U e (leafValues U b a₀) w : ℝ)) ≤
        rL * (TableModel.law (A := A) support p hp).expect (fun w => (leafCount support U e (leafValues U b a₀) w : ℝ)) ^ 2) :
    (TableModel.law (A := A) support p hp).expect (normalizedError support U e p hp a₀ b₀) ≤
      (∑ j, Real.sqrt (rE j)) + Real.sqrt rL := by
  let μ := TableModel.law (A := A) support p hp
  let M := μ.expect (fun w => (starCount (B := B) support U w : ℝ))
  have hE (j : B) : μ.expect (branchDeviation support U j
      (μ.expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ)))) ≤ Real.sqrt (rE j) * M := by
    have hh := expect_branchDeviation support U j p hp (fun _ => a₀) (hrE j) (hvE j)
    have hm := expect_starCount_branch support U j p hp (fun _ => a₀)
    dsimp only at hh hm
    change M = _ at hm
    rw [hm]
    convert hh using 1
    ring
  have hL : μ.expect (leafDeviation (B := B) support U e a₀
      (μ.expect (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ)))) ≤ Real.sqrt rL * M := by
    have hh := expect_leafDeviation (B := B) support U e p hp (leafValues U b₀ a₀)
      (leaf_pin_fieldwise U e b₀ a₀) a₀ hrL hvL
    have hm := expect_starCount_leaf support U e he p hp (leafValues U b₀ a₀)
      (leaf_pin_fieldwise U e b₀ a₀) a₀
    dsimp only at hh hm
    change M = _ at hm
    rw [hm]
    convert hh using 1
    ring
  unfold normalizedError
  rw [μ.expect_div, μ.expect_add, μ.expect_sum]
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ (∑ j, Real.sqrt (rE j) * M) + Real.sqrt rL * M :=
      add_le_add (Finset.sum_le_sum fun j _ => hE j) hL
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma starCount_lower (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) :
    (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)) -
      leafDeviation (B := B) support U e a₀ ((TableModel.law (A := A) support p hp).expect
        (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ))) w ≤
      (starCount (B := B) support U w : ℝ) := by
  rw [expect_starCount_leaf support U e he p hp (leafValues U b₀ a₀)
    (leaf_pin_fieldwise U e b₀ a₀) a₀, starCount_leaf support U e he w a₀]
  have hh := FiniteLaw.abs_sum_sub_const
    (fun b : B ↪ A => (leafCount support U e (leafValues U b a₀) w : ℝ))
    ((TableModel.law (A := A) support p hp).expect (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ)))
  have hlo := (abs_le.mp hh).1
  unfold leafDeviation
  linarith

lemma deviations_le_of_error (support : R → Finset F) (U : Finset F) (e : F)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) {ε : ℝ}
    (hM : 0 < (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)))
    (hε : normalizedError support U e p hp a₀ b₀ w ≤ ε) :
    (∀ j : B, branchDeviation support U j
      ((TableModel.law (A := A) support p hp).expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ))) w ≤
      ε * (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ))) ∧
    leafDeviation (B := B) support U e a₀ ((TableModel.law (A := A) support p hp).expect
      (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ))) w ≤
      ε * (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)) := by
  have hh := (div_le_iff₀ hM).mp hε
  constructor
  · intro j
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      branchDeviation_nonneg support U j
        ((TableModel.law (A := A) support p hp).expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ))) w)
      (Finset.mem_univ j)
    exact hsum.trans ((le_add_of_nonneg_right (leafDeviation_nonneg _ _ _ _ _ _)).trans hh)
  · exact (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => branchDeviation_nonneg _ _ _ _ _)).trans hh

lemma starCount_pos_of_error (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) {ε : ℝ} (hε1 : ε < 1)
    (hM : 0 < (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)))
    (hε : normalizedError support U e p hp a₀ b₀ w ≤ ε) :
    0 < starCount (B := B) support U w := by
  have hl := starCount_lower support U e he p hp a₀ b₀ w
  have hd := (deviations_le_of_error support U e p hp a₀ b₀ w hM hε).2
  have hs : 0 < (starCount (B := B) support U w : ℝ) := by nlinarith
  exact_mod_cast hs

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
