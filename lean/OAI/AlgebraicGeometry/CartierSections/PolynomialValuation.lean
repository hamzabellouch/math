import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Weighted valuations on polynomial rings

The least weight of a nonzero coefficient defines a valuation, including
weights with ties or zero coordinates. Nonnegative combinations of weight
vectors give a domination inequality within a fixed coordinate chart.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace CartierSections.Monomial

variable {σ k : Type*} [CommRing k]

/-- The value is the minimum monomial weight, with value infinity at zero. -/
def value (w : σ → ℝ≥0) (p : MvPolynomial σ k) : ENNReal :=
  p.support.inf fun d => (Finsupp.weight w d : ENNReal)

@[simp] lemma value_zero (w : σ → ℝ≥0) : value (k := k) w 0 = ⊤ := by
  simp [value]

lemma value_le_weight (w : σ → ℝ≥0) {p : MvPolynomial σ k} {d : σ →₀ ℕ}
    (hd : d ∈ p.support) : value w p ≤ (Finsupp.weight w d : ENNReal) :=
  Finset.inf_le hd

lemma le_value_iff (w : σ → ℝ≥0) {p : MvPolynomial σ k} {a : ENNReal} :
    a ≤ value w p ↔ ∀ d ∈ p.support, a ≤ (Finsupp.weight w d : ENNReal) :=
  Finset.le_inf_iff

lemma value_attained (w : σ → ℝ≥0) {p : MvPolynomial σ k} (hp : p ≠ 0) :
    ∃ d ∈ p.support, value w p = (Finsupp.weight w d : ENNReal) :=
  Finset.exists_mem_eq_inf p.support (MvPolynomial.support_nonempty.mpr hp) _

lemma value_lt_top (w : σ → ℝ≥0) {p : MvPolynomial σ k} (hp : p ≠ 0) :
    value w p < ⊤ := by
  obtain ⟨d, hd, he⟩ := value_attained w hp
  rw [he]
  exact ENNReal.coe_lt_top

@[simp] lemma value_one [Nontrivial k] (w : σ → ℝ≥0) : value (k := k) w 1 = 0 := by
  simp [value]

lemma value_add (w : σ → ℝ≥0) (p q : MvPolynomial σ k) :
    min (value w p) (value w q) ≤ value w (p+q) := by
  classical
  apply (le_value_iff w).mpr
  intro d hd
  have hd' := MvPolynomial.support_add hd
  rcases Finset.mem_union.mp hd' with hp | hq
  · exact (min_le_left _ _).trans (value_le_weight w hp)
  · exact (min_le_right _ _).trans (value_le_weight w hq)

/-- No cancellation can create a term below the sum of the two minima. -/
lemma le_value_mul (w : σ → ℝ≥0) (p q : MvPolynomial σ k) :
    value w p + value w q ≤ value w (p*q) := by
  classical
  apply (le_value_iff w).mpr
  intro d hd
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  subst d
  simpa only [map_add, ENNReal.coe_add] using
    add_le_add (value_le_weight w ha) (value_le_weight w hb)

/-- At the sum of the lower bounds, the initial part of a product is the
product of the initial parts. This includes non-generic tied weights. -/
lemma component_mul_at_lower_bounds (w : σ → ℝ≥0) (p q : MvPolynomial σ k)
    (a b : ℝ≥0)
    (hp : ∀ d ∈ p.support, a ≤ Finsupp.weight w d)
    (hq : ∀ d ∈ q.support, b ≤ Finsupp.weight w d) :
    MvPolynomial.weightedHomogeneousComponent w (a+b) (p*q) =
      MvPolynomial.weightedHomogeneousComponent w a p *
        MvPolynomial.weightedHomogeneousComponent w b q := by
  classical
  ext d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul]
  by_cases hd : Finsupp.weight w d = a+b
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [MvPolynomial.coeff_weightedHomogeneousComponent,
      MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hi : p.coeff ij.1 = 0
    · simp [hi]
    by_cases hj : q.coeff ij.2 = 0
    · simp [hj]
    have hi' := hp ij.1 (MvPolynomial.mem_support_iff.mpr hi)
    have hj' := hq ij.2 (MvPolynomial.mem_support_iff.mpr hj)
    have hs : Finsupp.weight w ij.1 + Finsupp.weight w ij.2 = a+b := by
      rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hij, hd]
    have hia : Finsupp.weight w ij.1 = a := le_antisymm
      (le_of_add_le_add_right ((add_le_add (le_refl (Finsupp.weight w ij.1)) hj').trans_eq hs)) hi'
    have hjb : Finsupp.weight w ij.2 = b := by
      rw [hia] at hs
      exact add_left_cancel hs
    simp [hia, hjb]
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro ij hij
    rw [MvPolynomial.coeff_weightedHomogeneousComponent,
      MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hi : Finsupp.weight w ij.1 = a
    · have hj : Finsupp.weight w ij.2 ≠ b := by
        intro hj
        apply hd
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij, map_add, hi, hj]
      simp [hj]
    · simp [hi]

lemma component_ne_zero_of_attained (w : σ → ℝ≥0) (p : MvPolynomial σ k)
    {d : σ →₀ ℕ} (hd : d ∈ p.support) :
    MvPolynomial.weightedHomogeneousComponent w (Finsupp.weight w d) p ≠ 0 := by
  classical
  intro h
  have hc := congrArg (fun p : MvPolynomial σ k => p.coeff d) h
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero] at hc
  exact MvPolynomial.mem_support_iff.mp hd hc

section Domain
variable [IsDomain k]

lemma value_mul (w : σ → ℝ≥0) (p q : MvPolynomial σ k) :
    value w (p*q) = value w p + value w q := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  obtain ⟨a, ha, hea⟩ := value_attained w hp
  obtain ⟨b, hb, heb⟩ := value_attained w hq
  apply le_antisymm _ (le_value_mul w p q)
  have hpa : ∀ d ∈ p.support, Finsupp.weight w a ≤ Finsupp.weight w d := by
    intro d hd
    exact ENNReal.coe_le_coe.mp (hea ▸ value_le_weight w hd)
  have hqb : ∀ d ∈ q.support, Finsupp.weight w b ≤ Finsupp.weight w d := by
    intro d hd
    exact ENNReal.coe_le_coe.mp (heb ▸ value_le_weight w hd)
  have hn : MvPolynomial.weightedHomogeneousComponent w
      (Finsupp.weight w a + Finsupp.weight w b) (p*q) ≠ 0 := by
    rw [component_mul_at_lower_bounds w p q _ _ hpa hqb]
    exact mul_ne_zero (component_ne_zero_of_attained w p ha)
      (component_ne_zero_of_attained w q hb)
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hn
  rw [MvPolynomial.support_weightedHomogeneousComponent, Finset.mem_filter] at hd
  rw [hea, heb, ← ENNReal.coe_add, ← hd.2]
  exact value_le_weight w hd.1

/-- Weighted monomial valuation on the genuine polynomial coordinate ring. -/
def valuation (w : σ → ℝ≥0) : AddValuation (MvPolynomial σ k) ENNReal :=
  AddValuation.of (value w) (value_zero w) (value_one w) (value_add w) (value_mul w)

@[simp] lemma valuation_apply (w : σ → ℝ≥0) (p : MvPolynomial σ k) :
    valuation w p = value w p := rfl

end Domain

section Convex
variable {ι : Type*}

/-- Coordinatewise nonnegative linear combination of weight vectors. -/
def combine (s : Finset ι) (c : ι → ℝ≥0) (w : ι → σ → ℝ≥0) : σ → ℝ≥0 :=
  fun j => ∑ i ∈ s, c i * w i j

lemma weight_combine (s : Finset ι) (c : ι → ℝ≥0) (w : ι → σ → ℝ≥0)
    (d : σ →₀ ℕ) :
    Finsupp.weight (combine s c w) d = ∑ i ∈ s, c i * Finsupp.weight (w i) d := by
  classical
  simp only [combine, Finsupp.weight_apply, Finsupp.sum,
    nsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Nonnegative combinations dominate the corresponding combination of values.
The homogeneous inequality needs no normalization of the coefficients. -/
lemma combine_dominates [IsDomain k] (s : Finset ι) (c : ι → ℝ≥0) (w : ι → σ → ℝ≥0)
    (p : MvPolynomial σ k) :
    ∑ i ∈ s, (c i : ENNReal) * valuation (w i) p ≤
      valuation (combine s c w) p := by
  change _ ≤ value _ p
  apply (le_value_iff _).mpr
  intro d hd
  rw [weight_combine, ENNReal.ofNNReal_finsetSum]
  simp_rw [ENNReal.coe_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_right (value_le_weight (w i) hd) _

/-- Equality of two monomial weights is preserved by nonnegative combinations. -/
lemma linear_equation_combine (s : Finset ι) (c : ι → ℝ≥0)
    (w : ι → σ → ℝ≥0) (a b : σ →₀ ℕ)
    (h : ∀ i ∈ s, Finsupp.weight (w i) a = Finsupp.weight (w i) b) :
    Finsupp.weight (combine s c w) a = Finsupp.weight (combine s c w) b := by
  rw [weight_combine, weight_combine]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

end Convex
end CartierSections.Monomial

end

end OAI
