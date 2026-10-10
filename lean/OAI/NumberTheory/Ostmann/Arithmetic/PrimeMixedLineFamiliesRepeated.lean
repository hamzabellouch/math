import OAI.NumberTheory.Ostmann.Arithmetic.PrimeMixedLineFamiliesProduct

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeMixedLineFamilies
open scoped BigOperators
variable {ι κ : Type*} (label : ι → κ) (p : κ → ℕ) [∀ k, Fact (p k).Prime]

def LabeledCommonZero
    (a b : ∀ k, {i // label i = k} → ZMod (p k))
    (z : ∀ k, ZMod (p k) × (ZMod (p k))ˣ) : Prop :=
  ∀ i, a (label i) ⟨i, rfl⟩ * ((z (label i)).1 : ZMod (p (label i))) +
    b (label i) ⟨i, rfl⟩ * ((z (label i)).2 : ZMod (p (label i))) = 0

theorem labeledCommonZero_iff
    (a b : ∀ k, {i // label i = k} → ZMod (p k))
    (z : ∀ k, ZMod (p k) × (ZMod (p k))ˣ) :
    LabeledCommonZero label p a b z ↔ ∀ k, CommonZero (a k) (b k) (z k) := by
  constructor
  · intro h k ⟨i, hi⟩
    subst k
    exact h i
  · intro h i
    exact h (label i) ⟨i, rfl⟩

def labeledEquiv (a b : ∀ k, {i // label i = k} → ZMod (p k)) :
    {z : ∀ k, ZMod (p k) × (ZMod (p k))ˣ // LabeledCommonZero label p a b z} ≃
      ∀ k, Solutions (a k) (b k) :=
  (Equiv.subtypeEquivRight (labeledCommonZero_iff label p a b)).trans
    (independentEquiv (fun k => {i // label i = k}) (fun k => ZMod (p k)) a b)

theorem labeled_probability [Fintype κ] [DecidableEq κ]
    (a b : ∀ k, {i // label i = k} → ZMod (p k)) :
    (Nat.card {z : ∀ k, ZMod (p k) × (ZMod (p k))ˣ //
      LabeledCommonZero label p a b z} : ℝ) /
      Fintype.card (∀ k, ZMod (p k) × (ZMod (p k))ˣ) =
      ∏ k, probability (p k) (a k) (b k) := by
  classical
  rw [Nat.card_congr (labeledEquiv label p a b), Nat.card_pi]
  simp only [Fintype.card_pi, Nat.cast_prod, probability, Finset.prod_div_distrib]

theorem representative_domination {η : Type*} [DecidableEq η] {J : Type*}
    (q : ℕ) [Fact q.Prime] (a b : J → ZMod q) (hz : ¬ AllZero a b)
    (s : Finset η) {i₀ : η} (hi₀ : i₀ ∈ s) {B : ℝ} (hB : 0 ≤ B)
    (μ : η → ℝ) (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hbound : ∀ i ∈ s, (q : ℝ) * μ i ≤ B) :
    ((∏ i ∈ s, μ i) * (q : ℝ) ^ s.card) * probability q a b ≤
      2 * μ i₀ * B ^ (s.card-1) := by
  have hq : 2 ≤ (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).two_le
  have hw : 0 ≤ (∏ i ∈ s, μ i) * (q : ℝ) ^ s.card :=
    mul_nonneg (Finset.prod_nonneg hμ) (pow_nonneg (Nat.cast_nonneg q) _)
  calc
    _ ≤ ((∏ i ∈ s, μ i) * (q : ℝ) ^ s.card) * ((q-1 : ℕ) : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (probability_le_unit_line q a b hz) hw
    _ = ((∏ i ∈ s, μ i) * (q : ℝ) ^ s.card) / ((q : ℝ)-1) := by
      rw [Nat.cast_sub (Fact.out : q.Prime).one_lt.le]
      simp only [Nat.cast_one, div_eq_mul_inv]
    _ ≤ _ := RepeatedLabels.representative_domination s hi₀ hq hB μ hμ hbound

end Ostmann.Arithmetic.PrimeMixedLineFamilies

end

end OAI
