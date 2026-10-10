import Mathlib
import OAI.Geometry.HyperbolicGroups.Deviation
import OAI.Geometry.HyperbolicGroups.FiberLaw

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

lemma sum_subtype_eq_ite {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : α → M) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) f).symm

namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

abbrev starCount (support : R → Finset F) (U : Finset F)
    (w : TableModel.Entry (A := A) support → Bool) := Fintype.card (Stars (B := B) support U w)

omit [DecidableEq R] in
lemma starCount_branch (support : R → Finset F) (U : Finset F) (j : B)
    (w : TableModel.Entry (A := A) support → Bool) :
    (starCount (B := B) support U w : ℝ) = ∑ σ : F → A, if TableModel.IsMatch support w σ then
      (extensionCount support U j (branchValues U σ) w : ℝ) else 0 := by
  classical
  calc
    _ = ∑ σ : Matches support w, (Fintype.card {z : Stars (B := B) support U w // starBranch support U w j z = σ} : ℝ) := by
      rw [← Nat.cast_sum,FiniteLaw.card_fibers]
    _ = ∑ σ : Matches support w, (extensionCount support U j (branchValues U σ.val) w : ℝ) := by
      simp only [card_branch_fiber]
    _ = _ := sum_subtype_eq_ite (TableModel.IsMatch support w)
      (fun σ : F → A => (extensionCount support U j (branchValues U σ) w : ℝ))

omit [DecidableEq R] in
lemma starCount_leaf (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (w : TableModel.Entry (A := A) support → Bool) (a₀ : A) :
    (starCount (B := B) support U w : ℝ) = ∑ b : B ↪ A, (leafCount support U e (leafValues U b a₀) w : ℝ) := by
  classical
  calc
    _ = ∑ b : B ↪ A, (Fintype.card {z : Stars (B := B) support U w // starLeaves support U e he w z = b} : ℝ) := by
      rw [← Nat.cast_sum,FiniteLaw.card_fibers]
    _ = _ := by simp only [card_leaf_fiber (a₀ := a₀)]

omit [DecidableEq R] in
lemma branchDeviation_subtype (support : R → Finset F) (U : Finset F) (j : B) (a : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) :
    branchDeviation support U j a w =
      ∑ σ : Matches support w, |(extensionCount support U j (branchValues U σ.val) w : ℝ) - a| :=
  (sum_subtype_eq_ite _ _).symm

lemma expect_starCount_branch (support : R → Finset F) (U : Finset F) (j : B)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (ξ : Var (B := B) U → A) :
    let μ := TableModel.law (A := A) support p hp
    μ.expect (fun w => (starCount (B := B) support U w : ℝ)) =
      ((Fintype.card (F → A) : ℝ) * ∏ r, p r) *
        μ.expect (fun w => (extensionCount support U j ξ w : ℝ)) := by
  dsimp only
  let μ := TableModel.law (A := A) support p hp
  simp_rw [starCount_branch support U j]
  rw [μ.expect_sum]
  have he (σ : F → A) : μ.expect (fun w => if TableModel.IsMatch support w σ then
      (extensionCount support U j (branchValues U σ) w : ℝ) else 0) =
      (∏ r, p r) * μ.expect (fun w => (extensionCount support U j ξ w : ℝ)) := by
    have hh := extension_conditioning support U j (branchValues (B := B) U σ) p hp (fun n => (n : ℝ))
    simp only [branchValues_coord] at hh
    exact hh.trans (congrArg ((∏ r, p r) * ·) (extension_expect_eq support U j _ ξ p hp))
  simp_rw [he]
  simp
  ring

lemma expect_starCount_leaf (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (ξ : Var (B := B) U → A)
    (hξ : PinnedAssignments.PinFieldwise (field U) (leafPins U e) ξ) (a₀ : A) :
    let μ := TableModel.law (A := A) support p hp
    μ.expect (fun w => (starCount (B := B) support U w : ℝ)) =
      (Fintype.card (B ↪ A) : ℝ) * μ.expect (fun w => (leafCount support U e ξ w : ℝ)) := by
  dsimp only
  let μ := TableModel.law (A := A) support p hp
  simp_rw [starCount_leaf support U e he _ a₀]
  rw [μ.expect_sum]
  have hh (b : B ↪ A) : μ.expect (fun w => (leafCount support U e (leafValues U b a₀) w : ℝ)) =
      μ.expect (fun w => (leafCount support U e ξ w : ℝ)) :=
    leaf_expect_eq support U e _ ξ p hp (leaf_pin_fieldwise U e b a₀) hξ
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rfl

lemma extensionMean_pos [Nonempty A] (support : R → Finset F) (U : Finset F) (j : B)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ r, 0 < p r)
    (ξ : Var (B := B) U → A) (hN : 4 * Fintype.card (Var (B := B) U) ≤ Fintype.card A) :
    0 < (TableModel.law (A := A) support p hp).expect (fun w => (extensionCount support U j ξ w : ℝ)) := by
  rw [extension_expect]
  apply mul_pos
  · have hh := PinnedAssignments.candidates_lower (field U) (branchPins U j) ξ (branch_pin_fieldwise U j ξ) hN
    have hn : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
    exact lt_of_lt_of_le (pow_pos (half_pos hn) _) hh
  · exact Finset.prod_pos fun s _ => hpos s.2.val

lemma starMean_pos [Nonempty A] (support : R → Finset F) (U : Finset F) (j : B)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ r, 0 < p r)
    (ξ : Var (B := B) U → A) (hN : 4 * Fintype.card (Var (B := B) U) ≤ Fintype.card A) :
    0 < (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)) := by
  rw [expect_starCount_branch (A := A) support U j p hp ξ]
  apply mul_pos
  · exact mul_pos (by exact_mod_cast Fintype.card_pos (α := F → A)) (Finset.prod_pos fun r _ => hpos r)
  · exact extensionMean_pos support U j p hp hpos ξ hN

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
