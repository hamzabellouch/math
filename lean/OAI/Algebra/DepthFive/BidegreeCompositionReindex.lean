import OAI.Algebra.DepthFive.ExponentCardinality

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

private theorem double_sum_coe_sort {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → β → ℝ) :
    (∑ x : s, ∑ y : t, f x y) = ∑ x ∈ s, ∑ y ∈ t, f x y := by
  rw [Finset.sum_coe_sort s (fun x => ∑ y : t, f x y)]
  apply Finset.sum_congr rfl
  intro x hx
  exact Finset.sum_coe_sort t (f x)

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Reindex a bidegree exponent by its two finite occupation antidiagonals. -/
def bidegreeAntidiagEquiv (side : σ → Bool) (a b : ℕ) :
    {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)} ≃
      (Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a) ×
      (Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b) :=
  (bidegreeExponentsEquiv side a b).trans
    (Equiv.prodCongr (homogeneousFunctionsEquivAntidiag a)
      (homogeneousFunctionsEquivAntidiag b))

theorem bidegreeAntidiagEquiv_join (side : σ → Bool) (a b : ℕ)
    (d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}) :
    (fun i => if h : side i = true then
      (bidegreeAntidiagEquiv side a b d).1.val ⟨i,h⟩ else
      (bidegreeAntidiagEquiv side a b d).2.val ⟨i,h⟩) = d.val := by
  funext i
  by_cases h : side i = true <;>
    simp [bidegreeAntidiagEquiv, bidegreeExponentsEquiv,
      homogeneousFunctionsEquivAntidiag, Equiv.subtypeProdEquivProd, h]

/-- Arbitrary, not necessarily separated, functions may be summed in the two groups. -/
theorem bidegree_sum_eq_double_antidiag (side : σ → Bool) (a b : ℕ)
    [Fintype {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}]
    (f : (σ → ℕ) → ℝ) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}, f d.val) =
      ∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a,
        ∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b,
          f (fun i => if h : side i = true then M ⟨i,h⟩ else N ⟨i,h⟩) := by
  let e := bidegreeAntidiagEquiv side a b
  have h := e.sum_comp (fun z => f (fun i =>
    if h : side i = true then z.1.val ⟨i,h⟩ else z.2.val ⟨i,h⟩))
  dsimp only [e] at h
  simp only [bidegreeAntidiagEquiv_join] at h
  rw [h, Fintype.sum_prod_type]
  exact double_sum_coe_sort
    (Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a)
    (Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b)
    (fun M N =>
    f (fun i => if h : side i = true then M ⟨i,h⟩ else N ⟨i,h⟩))

/-- Uniform bidegree averages are the nested uniform occupation means. -/
theorem bidegree_average_eq_double_antidiag (side : σ → Bool) (a b : ℕ)
    [Fintype {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}]
    (f : (σ → ℕ) → ℝ) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}, f d.val) /
      (Fintype.card {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)} : ℝ) =
      (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a,
        (∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b,
          f (fun i => if h : side i = true then M ⟨i,h⟩ else N ⟨i,h⟩)) /
          ((Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b).card : ℝ)) /
        ((Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a).card : ℝ) := by
  have hc := Fintype.card_congr (bidegreeAntidiagEquiv side a b)
  simp only [Fintype.card_prod, Fintype.card_coe] at hc
  rw [bidegree_sum_eq_double_antidiag, hc, Nat.cast_mul]
  rw [← Finset.sum_div, div_div, mul_comm]

end Problem335

end

end OAI
