import Mathlib

namespace OAI

/-! Harmonic collar weights with uniform total weight and quadratic cost. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology

open scoped BigOperators
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

def collarWeight (η : ℝ) (r j : ℕ) : ℝ := η / ((r+j:ℕ):ℝ)
def collarWeightSum (η : ℝ) (r n : ℕ) : ℝ := ∑ j ∈ Finset.range n, collarWeight η r j

def harmonicWindow (r n : ℕ) : ℝ := ∑ j ∈ Finset.range n, (((r+j:ℕ):ℝ))⁻¹

lemma harmonicWindow_block {r n : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    (1/3:ℝ) ≤ ∑ j ∈ Finset.range n, (((r+(n+j):ℕ):ℝ))⁻¹ := by
  have hn : 0 < n := lt_of_lt_of_le hr hrn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  calc
    (1/3:ℝ) = ∑ j ∈ Finset.range n, (3*(n:ℝ))⁻¹ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hd : (0:ℝ) < ((r+(n+j):ℕ):ℝ) := by positivity
      have hu : (((r+(n+j):ℕ):ℝ)) ≤ 3*(n:ℝ) := by exact_mod_cast (show r+(n+j) ≤ 3*n by omega)
      exact inv_anti₀ hd hu

lemma harmonicWindow_doubling {r : ℕ} (hr : 0 < r) (k : ℕ) :
    (k:ℝ)/3 ≤ harmonicWindow r (r*2^k) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_div]
    exact Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  | succ k ih =>
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by omega)
    have hn : r ≤ r*2^k := by nlinarith
    have hb := harmonicWindow_block hr hn
    have heq : r*2^(k+1) = r*2^k + r*2^k := by ring
    rw [heq, harmonicWindow, Finset.sum_range_add]
    simp only [harmonicWindow] at ih
    push_cast at ih hb ⊢
    linarith

lemma collarWeightSum_eq (η : ℝ) (r n : ℕ) :
    collarWeightSum η r n = η * harmonicWindow r n := by
  simp only [collarWeightSum, collarWeight, harmonicWindow, div_eq_mul_inv, Finset.mul_sum]

lemma collarWeight_pos {η : ℝ} (hη : 0 < η) {r : ℕ} (hr : 0 < r) (j : ℕ) :
    0 < collarWeight η r j := by unfold collarWeight; positivity

lemma collarWeight_le_one {η : ℝ} (hη : η ≤ 1) {r : ℕ} (hr : 0 < r) (j : ℕ) :
    collarWeight η r j ≤ 1 := by
  have hd : (1:ℝ) ≤ ((r+j:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ r+j by omega)
  unfold collarWeight
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
  simpa using hη.trans hd

theorem exists_uniform_collar_weights {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ r : ℕ, 0 < r →
      ∃ m : ℕ, 0 < m ∧ m ≤ M*r ∧
        (4:ℝ) ≤ collarWeightSum η r m ∧ collarWeightSum η r m ≤ 5 ∧
        (∀ j : Fin m, 0 < collarWeight η r j.val ∧ collarWeight η r j.val ≤ 1) ∧
        (∑ j : Fin m, (((r+j.val:ℕ):ℝ)) * (collarWeight η r j.val)^2) ≤ 5*η := by
  obtain ⟨K,hK⟩ := exists_nat_gt (12/η)
  have hK' : (4:ℝ) ≤ η * ((K:ℝ)/3) := by
    have hx := (div_lt_iff₀ hη).mp hK
    nlinarith
  refine ⟨2^K,by positivity,?_⟩
  intro r hr
  have hl : (4:ℝ) ≤ collarWeightSum η r (r*2^K) := by
    rw [collarWeightSum_eq]
    exact hK'.trans (mul_le_mul_of_nonneg_left (harmonicWindow_doubling hr K) hη.le)
  have hex : ∃ m : ℕ, (4:ℝ) ≤ collarWeightSum η r m := ⟨_,hl⟩
  let m := Nat.find hex
  have hlow : (4:ℝ) ≤ collarWeightSum η r m := Nat.find_spec hex
  have hm : m ≤ r*2^K := Nat.find_min' hex hl
  have hmpos : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    simp only [hz, collarWeightSum, Finset.range_zero, Finset.sum_empty] at hlow
    norm_num at hlow
  have hprev : collarWeightSum η r (m-1) < 4 :=
    lt_of_not_ge (Nat.find_min hex (by omega))
  have hs : collarWeightSum η r m = collarWeightSum η r (m-1) + collarWeight η r (m-1) := by
    conv_lhs => rw [show m = (m-1)+1 by omega]
    exact Finset.sum_range_succ _ _
  have hhigh : collarWeightSum η r m ≤ 5 := by
    have hw := collarWeight_le_one hη1 hr (m-1)
    rw [hs]
    linarith
  refine ⟨m,hmpos,by simpa [Nat.mul_comm] using hm,hlow,hhigh,?_,?_⟩
  · intro j
    exact ⟨collarWeight_pos hη hr _, collarWeight_le_one hη1 hr _⟩
  · have hw (j : Fin m) : (((r+j.val:ℕ):ℝ)) * (collarWeight η r j.val)^2 =
        η * collarWeight η r j.val := by
      have hd : (((r+j.val:ℕ):ℝ)) ≠ 0 := by positivity
      unfold collarWeight
      field_simp
    simp_rw [hw]
    rw [← Finset.mul_sum]
    have heq : (∑ j : Fin m, collarWeight η r j.val) = collarWeightSum η r m := by
      exact Fin.sum_univ_eq_sum_range (collarWeight η r) m
    rw [heq, mul_comm (5:ℝ) η]
    exact mul_le_mul_of_nonneg_left hhigh hη.le

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
