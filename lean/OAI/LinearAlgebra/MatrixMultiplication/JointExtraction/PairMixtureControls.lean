import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityControls
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityScaling

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointPairMixtureControls

open JointCompatibilityControls JointCompatibilityScaling
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A B : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
  [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]

def pairMixture (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (c : C) (ab : A c × B c) : ℝ :=
  (∑ u, (base c u : ℝ) * left c u ab.1 * right c u ab.2) / baseSize base c

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (B c)] in
theorem sum_first_fiber (c : C) (q : A c × B c → ℝ) (a : A c) :
    (∑ ab : {ab : A c × B c // ab.1 = a}, q ab.val) = ∑ b, q (a, b) := by
  let e : B c ≃ {ab : A c × B c // ab.1 = a} :=
    { toFun := fun b => ⟨(a, b), rfl⟩
      invFun := fun ab => ab.val.2
      left_inv := fun _ => rfl
      right_inv := fun ab => by apply Subtype.ext; exact Prod.ext ab.property.symm rfl }
  exact (e.sum_comp (fun ab => q ab.val)).symm

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (A c)] in
theorem sum_second_fiber (c : C) (q : A c × B c → ℝ) (b : B c) :
    (∑ ab : {ab : A c × B c // ab.2 = b}, q ab.val) = ∑ a, q (a, b) := by
  let e : A c ≃ {ab : A c × B c // ab.2 = b} :=
    { toFun := fun a => ⟨(a, b), rfl⟩
      invFun := fun ab => ab.val.1
      left_inv := fun _ => rfl
      right_inv := fun ab => by apply Subtype.ext; exact Prod.ext rfl ab.property.symm }
  exact (e.sum_comp (fun ab => q ab.val)).symm

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)] in
theorem base_eq_zero_of_size_eq_zero (base : ∀ c, Shape c → ℕ)
    (c : C) (hz : baseSize base c = 0) (u : Shape c) : base c u = 0 :=
  Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ u)).trans_eq hz)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem totalCenterCount_eq_zero_of_size_eq_zero (base : ∀ c, Shape c → ℕ)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (hz : baseSize base c = 0) (a : A c) :
    totalCenterCount base law c a = 0 := by
  simp only [totalCenterCount, base_eq_zero_of_size_eq_zero base c hz,
    Nat.cast_zero, zero_mul, Finset.sum_const_zero]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, DecidableEq (B c)] in
theorem pairMixture_left_balance (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (hnormalized : ∀ c u, 0 < base c u → ∑ b, right c u b = 1)
    (c : C) (a : A c) :
    (baseSize base c : ℝ) *
      (∑ ab : {ab : A c × B c // ab.1 = a}, pairMixture base left right c ab.val) =
      totalCenterCount base left c a := by
  rw [sum_first_fiber]
  simp only [pairMixture, ← Finset.sum_div]
  have hnum : (∑ b : B c, ∑ u : Shape c,
      (base c u : ℝ) * left c u a * right c u b) = totalCenterCount base left c a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : base c u = 0
    · simp [hu]
    · rw [← Finset.mul_sum, hnormalized c u (Nat.pos_of_ne_zero hu), mul_one]
  rw [hnum]
  by_cases hz : baseSize base c = 0
  · rw [totalCenterCount_eq_zero_of_size_eq_zero base left c hz a]
    simp
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, DecidableEq (A c)] in
theorem pairMixture_right_balance (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (hnormalized : ∀ c u, 0 < base c u → ∑ a, left c u a = 1)
    (c : C) (b : B c) :
    (baseSize base c : ℝ) *
      (∑ ab : {ab : A c × B c // ab.2 = b}, pairMixture base left right c ab.val) =
      totalCenterCount base right c b := by
  rw [sum_second_fiber]
  simp only [pairMixture, ← Finset.sum_div]
  have hnum : (∑ a : A c, ∑ u : Shape c,
      (base c u : ℝ) * left c u a * right c u b) = totalCenterCount base right c b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : base c u = 0
    · simp [hu]
    · rw [← Finset.sum_mul, ← Finset.mul_sum,
        hnormalized c u (Nat.pos_of_ne_zero hu), mul_one]
  rw [hnum]
  by_cases hz : baseSize base c = 0
  · rw [totalCenterCount_eq_zero_of_size_eq_zero base right c hz b]
    simp
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)

end MatrixMultiplication.JointPairMixtureControls

end

end OAI
