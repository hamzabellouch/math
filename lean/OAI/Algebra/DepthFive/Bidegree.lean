import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace Bidegree

open MvPolynomial Finsupp

variable {σ R : Type*} [CommSemiring R]

/-- The indicator weight of the derivative-variable side of a partition. -/
def weight (side : σ → Bool) (x : σ) : ℕ := if side x then 1 else 0

/-- Projection onto one degree in the selected variables. -/
def component (side : σ → Bool) (i : ℕ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  weightedHomogeneousComponent (weight side) i

@[simp] theorem coeff_component (side : σ → Bool) (i : ℕ)
    (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (component side i p).coeff d =
      if Finsupp.weight (weight side) d = i then p.coeff d else 0 :=
  coeff_weightedHomogeneousComponent i p d

theorem weight_add_complement (side : σ → Bool) (d : σ →₀ ℕ) :
    Finsupp.weight (weight side) d +
      Finsupp.weight (weight (fun x => !(side x))) d = d.degree := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases h : side x <;> simp [weight, h]

theorem weight_le_degree (side : σ → Bool) (d : σ →₀ ℕ) :
    Finsupp.weight (weight side) d ≤ d.degree := by
  have := weight_add_complement side d
  omega

theorem component_isWeightedHomogeneous (side : σ → Bool) (i : ℕ)
    (p : MvPolynomial σ R) :
    (component side i p).IsWeightedHomogeneous (weight side) i :=
  weightedHomogeneousComponent_isWeightedHomogeneous i p

theorem component_isHomogeneous (side : σ → Bool) (i : ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    (component side i p).IsHomogeneous n := by
  intro d hd
  apply hp
  intro hz
  simp [hz] at hd

theorem component_complement_degree (side : σ → Bool) (i : ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    (component side i p).IsWeightedHomogeneous (weight (fun x => !(side x))) (n - i) := by
  intro d hd
  have hi := component_isWeightedHomogeneous side i p hd
  have hn := component_isHomogeneous side i hp hd
  change Finsupp.weight (fun _ : σ => 1) d = n at hn
  have hsum := weight_add_complement side d
  rw [Finsupp.degree_eq_weight_one] at hsum
  omega

theorem component_eq_zero_of_lt (side : σ → Bool)
    {p : MvPolynomial σ R} {n i : ℕ} (hp : p.IsHomogeneous n) (hi : n < i) :
    component side i p = 0 := by
  ext d
  rw [coeff_component, AddMonoidAlgebra.coeff_zero]
  split_ifs with h
  · by_contra hz
    have hn := hp hz
    change Finsupp.weight (fun _ : σ => 1) d = n at hn
    have := weight_le_degree side d
    rw [Finsupp.degree_eq_weight_one] at this
    omega
  · rfl

/-- A homogeneous polynomial is the sum of its bidegree components. -/
theorem sum_components (side : σ → Bool) {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (∑ i ∈ Finset.range (n + 1), component side i p) = p := by
  classical
  ext d
  simp only [coeff_sum, coeff_component]
  by_cases hd : p.coeff d = 0
  · simp [hd]
  · have hn := hp hd
    change Finsupp.weight (fun _ : σ => 1) d = n at hn
    have hle := weight_le_degree side d
    rw [Finsupp.degree_eq_weight_one] at hle
    have hmem : Finsupp.weight (weight side) d ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single (Finsupp.weight (weight side) d)]
    · simp
    · intro b hb hne
      simp [Ne.symm hne]
    · exact fun h => (h hmem).elim

@[simp] theorem component_same (side : σ → Bool) {p : MvPolynomial σ R} {i : ℕ}
    (hp : p.IsWeightedHomogeneous (weight side) i) : component side i p = p :=
  hp.weightedHomogeneousComponent_same

theorem component_ne (side : σ → Bool) {p : MvPolynomial σ R} {i j : ℕ}
    (hp : p.IsWeightedHomogeneous (weight side) i) (hji : j ≠ i) :
    component side j p = 0 :=
  hp.weightedHomogeneousComponent_ne j hji

theorem component_of_weightedHomogeneous (side : σ → Bool)
    {p : MvPolynomial σ R} {i : ℕ}
    (hp : p.IsWeightedHomogeneous (weight side) i) (k : ℕ) :
    component side k p = if k = i then p else 0 := by
  classical
  exact weightedHomogeneousComponent_of_mem hp

/-- Distributing a finite product over all choices of bidegrees. -/
theorem prod_eq_sum_components {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : σ → Bool) (p : ι → MvPolynomial σ R) (e : ι → ℕ)
    (hp : ∀ a, (p a).IsHomogeneous (e a)) :
    (∏ a, p a) =
      ∑ f ∈ Fintype.piFinset (fun a => Finset.range (e a + 1)),
        ∏ a, component side (f a) (p a) := by
  classical
  calc
    (∏ a, p a) = ∏ a, ∑ i ∈ Finset.range (e a + 1), component side i (p a) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact (sum_components side (hp a)).symm
    _ = _ := Finset.prod_univ_sum _ _

/-- Projection of the product keeps exactly degree assignments whose sum is `k`. -/
theorem component_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : σ → Bool) (p : ι → MvPolynomial σ R) (e : ι → ℕ)
    (hp : ∀ a, (p a).IsHomogeneous (e a)) (k : ℕ) :
    component side k (∏ a, p a) =
      ∑ f ∈ Fintype.piFinset (fun a => Finset.range (e a + 1)),
        if (∑ a, f a) = k then ∏ a, component side (f a) (p a) else 0 := by
  classical
  rw [prod_eq_sum_components side p e hp, map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  have hprod : (∏ a, component side (f a) (p a)).IsWeightedHomogeneous
      (weight side) (∑ a, f a) := by
    exact IsWeightedHomogeneous.prod _ _ _ (fun a ha =>
      component_isWeightedHomogeneous side (f a) (p a))
  rw [component_of_weightedHomogeneous side hprod]
  simp only [eq_comm]

end Bidegree
end Problem335

end

end OAI
