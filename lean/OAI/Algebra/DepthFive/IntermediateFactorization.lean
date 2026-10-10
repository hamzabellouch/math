import OAI.Algebra.DepthFive.MixedOperator
import OAI.Algebra.DepthFive.OperatorRank
import OAI.Algebra.DepthFive.MixedOperatorBidegree
import OAI.Algebra.DepthFive.RankMeasure

namespace OAI

/-! Factorization of mixed operators through intermediate bidegree spaces.
The codomain is initially the full polynomial space.  Restricting it to a
bidegree submodule leaves the range dimension unchanged, as proved below. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*} [Field K]

/-- The full operator restricted to a finite-bidegree source, as a linear
family in the polynomial defining the operator. -/
def sourceMixedOperator (isV : σ → Bool) (a b : ℕ) :
    MvPolynomial σ K →ₗ[K]
      (bidegreeSubmodule (K := K) isV a b →ₗ[K] MvPolynomial σ K) where
  toFun p := (mixedOperator isV p).comp (bidegreeSubmodule isV a b).subtype
  map_add' p q := by
    ext f
    simp
  map_smul' c p := by
    ext f
    simp

@[simp] theorem sourceMixedOperator_apply (isV : σ → Bool) (a b : ℕ)
    (p : MvPolynomial σ K) (f : bidegreeSubmodule (K := K) isV a b) :
    sourceMixedOperator isV a b p f = mixedOperator isV p (f : MvPolynomial σ K) := rfl

/-- The operator for `p` maps the source into the proposed intermediate space. -/
def intermediateStart (isV : σ → Bool) (a b c d : ℕ)
    (p : MvPolynomial σ K)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV p (f : MvPolynomial σ K) ∈ bidegreeSubmodule isV c d) :
    bidegreeSubmodule (K := K) isV a b →ₗ[K] bidegreeSubmodule (K := K) isV c d :=
  LinearMap.codRestrict _ (sourceMixedOperator isV a b p) h

/-- Factorization is an equality of actual linear maps, not merely a rank
inequality.  The rightmost polynomial factor operates first. -/
theorem sourceMixedOperator_mul_factorization (isV : σ → Bool) (a b c d : ℕ)
    (p q : MvPolynomial σ K)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV p (f : MvPolynomial σ K) ∈ bidegreeSubmodule isV c d) :
    sourceMixedOperator isV a b (q * p) =
      (sourceMixedOperator isV c d q).comp
        (intermediateStart isV a b c d p h) := by
  apply LinearMap.ext
  intro f
  exact mixedOperator_mul_apply isV q p f

/-- Any factorization through an intermediate bidegree space bounds rank by
that space's dimension. -/
theorem sourceMixedOperator_mul_rank_le [Finite σ]
    (isV : σ → Bool) (a b c d : ℕ) (p q : MvPolynomial σ K)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV p (f : MvPolynomial σ K) ∈ bidegreeSubmodule isV c d) :
    RankMeasure.mapRank (sourceMixedOperator isV a b (q * p)) ≤
      Module.finrank K (bidegreeSubmodule (K := K) isV c d) := by
  rw [sourceMixedOperator_mul_factorization isV a b c d p q h]
  exact RankMeasure.mapRank_factor_le _ _

/-- The bidegree of a selected subproduct is the sum of the selected
bidegrees, with no condition on the unselected factors. -/
theorem selected_bidegree_product_mem {ι : Type*} (s : Finset ι)
    (selected : ι → Prop) [DecidablePred selected]
    (Q : ι → MvPolynomial σ K) (i j : ι → ℕ) (isV : σ → Bool)
    (hQ : ∀ l ∈ s, Q l ∈ bidegreeSubmodule isV (i l) (j l)) :
    (∏ l ∈ s.filter selected, Q l) ∈
      bidegreeSubmodule isV (∑ l ∈ s.filter selected, i l)
        (∑ l ∈ s.filter selected, j l) := by
  have hp := MvPolynomial.IsWeightedHomogeneous.prod (s.filter selected) Q
    (fun l => (i l, j l)) (w := bidegreeWeight isV)
    (fun l hl => hQ l (Finset.mem_filter.mp hl).1)
  rw [← prod_mk_sum] at hp
  exact hp

/-- In a commutative polynomial product, any chosen group of factors can be
applied first.  In the product-rank proof this group consists of the factors
with positive proportional bidegree discrepancy. -/
theorem sourceMixedOperator_prod_rank_le [Finite σ] {ι : Type*}
    (s : Finset ι) (selected : ι → Prop) [DecidablePred selected]
    (Q : ι → MvPolynomial σ K) (isV : σ → Bool) (a b c d : ℕ)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV (∏ j ∈ s.filter selected, Q j) (f : MvPolynomial σ K) ∈
        bidegreeSubmodule isV c d) :
    RankMeasure.mapRank (sourceMixedOperator isV a b (∏ j ∈ s, Q j)) ≤
      Module.finrank K (bidegreeSubmodule (K := K) isV c d) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not s selected Q, mul_comm]
  exact sourceMixedOperator_mul_rank_le isV a b c d _ _ h

/-- A selected homogeneous subproduct gives the actual intermediate dimension
bound.  Only its total derivative degree needs to fit inside the source. -/
theorem sourceMixedOperator_homogeneous_prod_rank_le [Finite σ] {ι : Type*}
    (s : Finset ι) (selected : ι → Prop) [DecidablePred selected]
    (Q : ι → MvPolynomial σ K) (i j : ι → ℕ) (isV : σ → Bool) (a b : ℕ)
    (hQ : ∀ l ∈ s, Q l ∈ bidegreeSubmodule isV (i l) (j l))
    (hi : (∑ l ∈ s.filter selected, i l) ≤ a) :
    RankMeasure.mapRank (sourceMixedOperator isV a b (∏ l ∈ s, Q l)) ≤
      Module.finrank K (bidegreeSubmodule (K := K) isV
        (a - ∑ l ∈ s.filter selected, i l)
        (b + ∑ l ∈ s.filter selected, j l)) := by
  apply sourceMixedOperator_prod_rank_le s selected Q isV a b
  intro f
  exact mixedOperator_mem_bidegreeSubmodule isV hi
    (selected_bidegree_product_mem s selected Q i j isV hQ) f.property

/-- Specialization to the component product belonging to one bidegree
assignment.  This is the geometric rank estimate used before summing over
assignments in the product-rank lemma. -/
theorem sourceMixedOperator_component_prod_rank_le [Finite σ] {ι : Type*}
    (s : Finset ι) (selected : ι → Prop) [DecidablePred selected]
    (Q : ι → MvPolynomial σ K) (e i : ι → ℕ) (isV : σ → Bool) (a b : ℕ)
    (hi : (∑ l ∈ s.filter selected, i l) ≤ a) :
    RankMeasure.mapRank (sourceMixedOperator isV a b
      (∏ l ∈ s, bidegreeComponent isV (i l) (e l - i l) (Q l))) ≤
      Module.finrank K (bidegreeSubmodule (K := K) isV
        (a - ∑ l ∈ s.filter selected, i l)
        (b + ∑ l ∈ s.filter selected, (e l - i l))) := by
  exact sourceMixedOperator_homogeneous_prod_rank_le s selected
    (fun l => bidegreeComponent isV (i l) (e l - i l) (Q l))
    i (fun l => e l - i l) isV a b
    (fun l _ => bidegreeComponent_mem isV (i l) (e l - i l) (Q l)) hi

/-- A total derivative-degree bound suffices for every selection of factors.
This version is convenient for constrained assignments whose degrees sum to `k`. -/
theorem sourceMixedOperator_component_prod_rank_le_of_sum_le [Finite σ]
    {ι : Type*} (s : Finset ι) (selected : ι → Prop) [DecidablePred selected]
    (Q : ι → MvPolynomial σ K) (e i : ι → ℕ) (isV : σ → Bool) (a b : ℕ)
    (hi : (∑ l ∈ s, i l) ≤ a) :
    RankMeasure.mapRank (sourceMixedOperator isV a b
      (∏ l ∈ s, bidegreeComponent isV (i l) (e l - i l) (Q l))) ≤
      Module.finrank K (bidegreeSubmodule (K := K) isV
        (a - ∑ l ∈ s.filter selected, i l)
        (b + ∑ l ∈ s.filter selected, (e l - i l))) := by
  apply sourceMixedOperator_component_prod_rank_le s selected Q e i isV a b
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.zero_le _)).trans hi

/-- Passing from a fixed-bidegree codomain to the full polynomial codomain
does not alter the dimension of the range. -/
theorem mapRank_subtype_comp {V : Type*} [AddCommGroup V] [Module K V]
    (Z : Submodule K (MvPolynomial σ K)) (f : V →ₗ[K] Z) :
    RankMeasure.mapRank (Z.subtype.comp f) = RankMeasure.mapRank f := by
  unfold RankMeasure.mapRank
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_subtype_eq Z f.range

/-- Consequently a codomain-restricted mixed operator and its source-only
restriction have exactly the same rank. -/
theorem sourceMixedOperator_codRestrict_rank (isV : σ → Bool) (a b c d : ℕ)
    (p : MvPolynomial σ K)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV p (f : MvPolynomial σ K) ∈ bidegreeSubmodule isV c d) :
    RankMeasure.mapRank (intermediateStart isV a b c d p h) =
      RankMeasure.mapRank (sourceMixedOperator isV a b p) := by
  have heq : (bidegreeSubmodule (K := K) isV c d).subtype.comp
      (intermediateStart isV a b c d p h) =
      sourceMixedOperator isV a b p := by
    apply LinearMap.ext
    intro f
    rfl
  rw [← heq]
  exact (mapRank_subtype_comp _ _).symm

end Problem335

end

end OAI
