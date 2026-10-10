import OAI.NumberTheory.Jacobsthal.Estimates.HarmonicConditioning
import OAI.NumberTheory.Jacobsthal.Estimates.SourceInitialDiscard

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

theorem weighted_to_count_density {α : Type*} (A B : Finset α) (hB : B ⊆ A) (hA : 0 < A.card)
    (w : α → ℝ) (G rho : ℝ) (hG : 0 < G) (hTotal : 0 < ∑ a ∈ A,w a)
    (hspread : ∀ a ∈ A,∀ b ∈ A,w a ≤ G*w b)
    (hweighted : rho*(∑ a ∈ A,w a) ≤ ∑ b ∈ B,w b) :
    (rho/G)*(A.card : ℝ) ≤ (B.card : ℝ) := by
  have hspreadSum := subset_weight_spread A B hB hA w G hspread
  have hcoef : rho ≤ (B.card : ℝ)*G/(A.card : ℝ) :=
    le_of_mul_le_mul_right (hweighted.trans hspreadSum) hTotal
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hmul := (le_div_iff₀ hApos).mp hcoef
  calc
    _ = (rho*(A.card : ℝ))/G := by ring
    _ ≤ (B.card : ℝ) := (div_le_iff₀ hG).mpr hmul

end ErdosInverseCells

end

section

namespace ErdosInverseCells
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem triple_weight_spread (P Q U : Finset ℕ) (xi : ℝ) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hP : ∀ p ∈ P,∀ r ∈ P,(p : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hQ : ∀ q ∈ Q,∀ r ∈ Q,(q : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hU : ∀ u ∈ U,∀ r ∈ U,(u : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹) :
    ∀ x ∈ tripleSpace P Q U,∀ y ∈ tripleSpace P Q U,tripleWeight x ≤ 8*tripleWeight y := by
  intro x hx y hy
  have hx' : x.1.1 ∈ P ∧ x.1.2 ∈ Q ∧ x.2 ∈ U := by
    simpa only [tripleSpace,Finset.mem_product,and_assoc] using hx
  have hy' : y.1.1 ∈ P ∧ y.1.2 ∈ Q ∧ y.2 ∈ U := by
    simpa only [tripleSpace,Finset.mem_product,and_assoc] using hy
  have h1 := hP _ hx'.1 _ hy'.1
  have h2 := hQ _ hx'.2.1 _ hy'.2.1
  have h3 := hU _ hx'.2.2 _ hy'.2.2
  have hc : (1+xi)^3 ≤ (8 : ℝ) := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 1+xi) (by linarith : 1+xi ≤ 2) 3
    norm_num at hh
    exact hh
  calc
    _ ≤ ((1+xi)*(y.1.1 : ℝ)⁻¹)*((1+xi)*(y.1.2 : ℝ)⁻¹)*((1+xi)*(y.2 : ℝ)⁻¹) :=
      mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    _ = (1+xi)^3*tripleWeight y := by unfold tripleWeight;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (tripleWeight_nonneg y)

theorem triple_weighted_to_count (P Q U : Finset ℕ) (xi sigma : ℝ) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (witness : (ℕ × ℕ) → ℕ → Prop)
    (hPpos : 0 < harmonicMass P) (hQpos : 0 < harmonicMass Q) (hUpos : 0 < harmonicMass U)
    (hP : ∀ p ∈ P,∀ r ∈ P,(p : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hQ : ∀ q ∈ Q,∀ r ∈ Q,(q : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hU : ∀ u ∈ U,∀ r ∈ U,(u : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hweighted : (sigma/2)*(harmonicMass P*harmonicMass Q*harmonicMass U) ≤ weightedWitness P Q U witness) :
    (sigma/16)*((P.product Q).card : ℝ)*(U.card : ℝ) ≤
      ((witnessPairs (P.product Q) U witness).card : ℝ) := by
  have hTotal : 0 < ∑ x ∈ tripleSpace P Q U,tripleWeight x := by
    rw [triple_weight_sum]
    exact mul_pos (mul_pos hPpos hQpos) hUpos
  have hA : 0 < (tripleSpace P Q U).card := by
    by_contra hn
    have he : tripleSpace P Q U = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he,Finset.sum_empty] at hTotal
    linarith
  have hsub : witnessPairs (P.product Q) U witness ⊆ tripleSpace P Q U := Finset.filter_subset _ _
  have hh := weighted_to_count_density (tripleSpace P Q U) (witnessPairs (P.product Q) U witness)
    hsub hA tripleWeight 8 (sigma/2) (by norm_num) hTotal (triple_weight_spread P Q U xi hxi hxi1 hP hQ hU)
    (by simpa only [triple_weight_sum,weightedWitness] using hweighted)
  simpa only [tripleSpace,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,div_div,show (2 : ℝ)*8 = 16 by norm_num,mul_assoc] using hh

end ErdosInverseCells

end

end Erdos970

end OAI
