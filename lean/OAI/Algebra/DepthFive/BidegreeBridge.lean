import OAI.Algebra.DepthFive.Bidegree
import OAI.Algebra.DepthFive.OperatorRank

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open MvPolynomial
variable {σ R : Type*} [CommSemiring R]

/-- The paired weight is exactly the two complementary indicator weights. -/
theorem bidegreeWeight_eq_pair (side : σ → Bool) (d : σ →₀ ℕ) :
    Finsupp.weight (bidegreeWeight side) d =
      (Finsupp.weight (Bidegree.weight side) d,
       Finsupp.weight (Bidegree.weight (fun x => !(side x))) d) := by
  classical
  apply Prod.ext <;>
    simp only [Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum, Prod.snd_sum,
      Prod.smul_fst, Prod.smul_snd] <;>
    apply Finset.sum_congr rfl <;>
    intro x hx <;>
    cases h : side x <;> simp [bidegreeWeight, Bidegree.weight, h]

theorem mem_bidegreeSubmodule_iff_indicator (side : σ → Bool) (i j : ℕ)
    (p : MvPolynomial σ R) :
    p ∈ bidegreeSubmodule side i j ↔
      p.IsWeightedHomogeneous (Bidegree.weight side) i ∧
      p.IsWeightedHomogeneous (Bidegree.weight (fun x => !(side x))) j := by
  constructor
  · intro h
    constructor
    · intro d hd
      have hh := h hd
      rw [bidegreeWeight_eq_pair] at hh
      exact congrArg Prod.fst hh
    · intro d hd
      have hh := h hd
      rw [bidegreeWeight_eq_pair] at hh
      exact congrArg Prod.snd hh
  · rintro ⟨h₁, h₂⟩ d hd
    rw [bidegreeWeight_eq_pair, h₁ hd, h₂ hd]

/-- On total degree `n`, a single degree projection already fixes the other degree. -/
theorem bidegreeComponent_sub_eq_component (side : σ → Bool) (i : ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    bidegreeComponent side i (n - i) p = Bidegree.component side i p := by
  classical
  ext d
  rw [coeff_bidegreeComponent, Bidegree.coeff_component, bidegreeWeight_eq_pair]
  by_cases hz : p.coeff d = 0
  · simp [hz]
  · have hn := hp hz
    change Finsupp.weight (fun _ : σ => 1) d = n at hn
    have hsum := Bidegree.weight_add_complement side d
    rw [Finsupp.degree_eq_weight_one] at hsum
    by_cases hi : Finsupp.weight (Bidegree.weight side) d = i
    · have hj : Finsupp.weight (Bidegree.weight (fun x => !(side x))) d = n - i := by
        omega
      simp [hi, hj]
    · simp [hi]

theorem bidegreeComponent_eq_component (side : σ → Bool) (i j : ℕ)
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous (i + j)) :
    bidegreeComponent side i j p = Bidegree.component side i p := by
  simpa only [Nat.add_sub_cancel_left] using bidegreeComponent_sub_eq_component side i hp

theorem component_mem_bidegreeSubmodule (side : σ → Bool) (i : ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    Bidegree.component side i p ∈ bidegreeSubmodule side i (n - i) := by
  rw [← bidegreeComponent_sub_eq_component side i hp]
  exact bidegreeComponent_mem side i (n - i) p

theorem sum_bidegreeComponents (side : σ → Bool)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    (∑ i ∈ Finset.range (n + 1), bidegreeComponent side i (n - i) p) = p := by
  simp_rw [bidegreeComponent_sub_eq_component side _ hp]
  exact Bidegree.sum_components side hp

/-- The product-rank expansion, expressed in the paired bidegree API. -/
theorem bidegreeComponent_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : σ → Bool) (p : ι → MvPolynomial σ R) (e : ι → ℕ)
    (hp : ∀ a, (p a).IsHomogeneous (e a)) (k m : ℕ)
    (hkm : k + m = ∑ a, e a) :
    bidegreeComponent side k m (∏ a, p a) =
      ∑ f ∈ Fintype.piFinset (fun a => Finset.range (e a + 1)),
        if (∑ a, f a) = k then
          ∏ a, bidegreeComponent side (f a) (e a - f a) (p a) else 0 := by
  classical
  have htotal : (∏ a, p a).IsHomogeneous (k + m) := by
    rw [hkm]
    exact IsHomogeneous.prod _ _ _ (fun a ha => hp a)
  rw [bidegreeComponent_eq_component side k m htotal,
    Bidegree.component_prod side p e hp k]
  simp_rw [bidegreeComponent_sub_eq_component side _ (hp _)]

/-- A summand in the constrained expansion has the intended target bidegree. -/
theorem component_product_mem_bidegree {ι : Type*} [Fintype ι]
    (side : σ → Bool) (p : ι → MvPolynomial σ R) (e f : ι → ℕ)
    (hp : ∀ a, (p a).IsHomogeneous (e a)) (k m : ℕ)
    (hkm : k + m = ∑ a, e a) (hf : ∑ a, f a = k) :
    (∏ a, Bidegree.component side (f a) (p a)) ∈ bidegreeSubmodule side k m := by
  classical
  let q := ∏ a, Bidegree.component side (f a) (p a)
  have htotal : q.IsHomogeneous (k + m) := by
    rw [hkm]
    exact IsHomogeneous.prod _ _ _ (fun a ha =>
      Bidegree.component_isHomogeneous side (f a) (hp a))
  have hweight : q.IsWeightedHomogeneous (Bidegree.weight side) k := by
    rw [← hf]
    exact IsWeightedHomogeneous.prod _ _ _ (fun a ha =>
      Bidegree.component_isWeightedHomogeneous side (f a) (p a))
  have heq : bidegreeComponent side k m q = q := by
    rw [bidegreeComponent_eq_component side k m htotal,
      Bidegree.component_same side hweight]
  change q ∈ bidegreeSubmodule side k m
  rw [← heq]
  exact bidegreeComponent_mem side k m q

end Problem335

end

end OAI
