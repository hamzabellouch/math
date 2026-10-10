import OAI.Algebra.DepthFive.OperatorRank
import OAI.Algebra.DepthFive.ShiftedOccupation

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace ShiftedOccupation

lemma bidegreeWeight_eq_of_layer_sums {ι σ : Type*} [Fintype ι] [Fintype σ]
    (side : ι → Bool) (M N : (ι × σ) →₀ ℕ)
    (h : ∀ t, (∑ a : σ, M (t, a)) = ∑ a : σ, N (t, a)) :
    Finsupp.weight (bidegreeWeight (fun x : ι × σ => side x.1)) M =
      Finsupp.weight (bidegreeWeight (fun x : ι × σ => side x.1)) N := by
  classical
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t ht
  change (∑ x : σ, M (t, x) • (if side t then (1, 0) else (0, 1) : ℕ × ℕ)) =
    ∑ x : σ, N (t, x) • (if side t then (1, 0) else (0, 1) : ℕ × ℕ)
  rw [← Finset.sum_smul, ← Finset.sum_smul, h t]

/-- A natural shifted occupation, represented in the canonical finite-exponent type. -/
def sourceFinsupp {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (M : (ι × σ) →₀ ℕ) (sign : ι → ℤ) (p q : ι → σ) : (ι × σ) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (source M sign p q)

@[simp] lemma sourceFinsupp_apply {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq σ] (M : (ι × σ) →₀ ℕ) (sign : ι → ℤ) (p q : ι → σ)
    (x : ι × σ) : sourceFinsupp M sign p q x = source M sign p q x := by
  simp [sourceFinsupp]

lemma sourceFinsupp_bidegree {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq σ] (side : ι → Bool) (M : (ι × σ) →₀ ℕ)
    (sign : ι → ℤ) (p q : ι → σ)
    (h : ∀ x, 0 ≤ signedSource M sign p q x) :
    Finsupp.weight (bidegreeWeight (fun x : ι × σ => side x.1))
        (sourceFinsupp M sign p q) =
      Finsupp.weight (bidegreeWeight (fun x : ι × σ => side x.1)) M := by
  apply bidegreeWeight_eq_of_layer_sums
  intro t
  simpa using source_layer_sum M sign p q h t

/-- Existence inside the exact bidegree-index subtype is equivalent to coordinate nonnegativity. -/
theorem exists_bidegree_source_iff {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq σ] (side : ι → Bool) (a b : ℕ)
    (M : (ι × σ) →₀ ℕ)
    (hM : Finsupp.weight (bidegreeWeight (fun x : ι × σ => side x.1)) M = (a, b))
    (sign : ι → ℤ) (p q : ι → σ) :
    (∃ N : {d : (ι × σ) →₀ ℕ |
        Finsupp.weight (bidegreeWeight (fun x : ι × σ => side x.1)) d = (a, b)},
      ∀ x, ((N.1 x : ℕ) : ℤ) = signedSource M sign p q x) ↔
      ∀ x, 0 ≤ signedSource M sign p q x := by
  constructor
  · rintro ⟨N, hN⟩ x
    rw [← hN x]
    positivity
  · intro h
    refine ⟨⟨sourceFinsupp M sign p q, ?_⟩, ?_⟩
    · exact (sourceFinsupp_bidegree side M sign p q h).trans hM
    · intro x
      simp only [sourceFinsupp_apply]
      exact source_cast M sign p q h x

/-- The canonical source exponent subtype used by the bidegree monomial basis. -/
abbrev BidegreeSource {ι σ : Type*} (side : ι → Bool) (a b : ℕ) :=
  {d : (ι × σ) →₀ ℕ |
    Finsupp.weight (bidegreeWeight (fun x : ι × σ => side x.1)) d = (a, b)}

def sourceEmbedding {ι σ : Type*} {side : ι → Bool} {a b : ℕ}
    (d : BidegreeSource (σ := σ) side a b) : ι × σ → ℤ :=
  fun x => (d.1 x : ℤ)

lemma sourceEmbedding_injective {ι σ : Type*} {side : ι → Bool} {a b : ℕ} :
    Function.Injective (@sourceEmbedding ι σ side a b) := by
  intro M N h
  apply Subtype.ext
  apply Finsupp.ext
  intro x
  have hx := congrFun h x
  change (M.1 x : ℤ) = (N.1 x : ℤ) at hx
  exact_mod_cast hx

/-- The unique shifted source as an element of the original bidegree domain. -/
def sourceIndex {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    {side : ι → Bool} {a b : ℕ} (M : BidegreeSource (σ := σ) side a b)
    (sign : ι → ℤ) (p q : ι → σ)
    (h : ∀ x, 0 ≤ signedSource M.1 sign p q x) : BidegreeSource (σ := σ) side a b :=
  ⟨sourceFinsupp M.1 sign p q, (sourceFinsupp_bidegree side M.1 sign p q h).trans M.2⟩

lemma sourceIndex_embedding {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    {side : ι → Bool} {a b : ℕ} (M : BidegreeSource (σ := σ) side a b)
    (sign : ι → ℤ) (p q : ι → σ)
    (h : ∀ x, 0 ≤ signedSource M.1 sign p q x) :
    sourceEmbedding (sourceIndex M sign p q h) = signedSource M.1 sign p q := by
  funext x
  exact source_cast M.1 sign p q h x

lemma extend_source_valid {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    {side : ι → Bool} {a b : ℕ} (M : BidegreeSource (σ := σ) side a b)
    (sign : ι → ℤ) (p q : ι → σ)
    (h : ∀ x, 0 ≤ signedSource M.1 sign p q x)
    (w : BidegreeSource (σ := σ) side a b → ℝ) :
    Function.extend sourceEmbedding w (fun _ => 0) (signedSource M.1 sign p q) =
      w (sourceIndex M sign p q h) := by
  rw [← sourceIndex_embedding M sign p q h]
  exact sourceEmbedding_injective.extend_apply _ _ _

lemma extend_source_invalid {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    {side : ι → Bool} {a b : ℕ} (M : BidegreeSource (σ := σ) side a b)
    (sign : ι → ℤ) (p q : ι → σ)
    (h : ¬ ∀ x, 0 ≤ signedSource M.1 sign p q x)
    (w : BidegreeSource (σ := σ) side a b → ℝ) :
    Function.extend sourceEmbedding w (fun _ => 0) (signedSource M.1 sign p q) = 0 := by
  apply Function.extend_apply'
  rintro ⟨N, hN⟩
  apply h
  intro x
  have hx := congrFun hN x
  rw [← hx]
  exact Int.natCast_nonneg _

end ShiftedOccupation
end Problem335

end

end OAI
