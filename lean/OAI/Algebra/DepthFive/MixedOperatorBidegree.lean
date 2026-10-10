import OAI.Algebra.DepthFive.OperatorHomogeneity
import OAI.Algebra.DepthFive.OperatorRank

namespace OAI

/-! The mixed operator restricts to the finite bidegree spaces used by the rank measure. -/

noncomputable section

namespace Problem335

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

private theorem weight_map_hom {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : A →+ B) (w : σ → A) (e : σ →₀ ℕ) :
    Finsupp.weight (f ∘ w) e = f (Finsupp.weight w e) := by
  simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]

private theorem weighted_homogeneous_map {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : A →+ B) {w : σ → A} {p : MvPolynomial σ K} {d : A}
    (hp : p.IsWeightedHomogeneous w d) :
    p.IsWeightedHomogeneous (f ∘ w) (f d) := by
  intro e he
  rw [weight_map_hom, hp he]

private def bidegreeCast : ℕ × ℕ →+ ℤ × ℤ :=
  (Nat.castAddMonoidHom ℤ).prodMap (Nat.castAddMonoidHom ℤ)

private def bidegreeSign : ℕ × ℕ →+ ℤ × ℤ :=
  (-Nat.castAddMonoidHom ℤ).prodMap (Nat.castAddMonoidHom ℤ)

private theorem bidegreeCast_injective : Function.Injective bidegreeCast := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simpa [bidegreeCast] using h

private theorem operatorWeight_bidegree (isV : σ → Bool) :
    operatorWeight isV (bidegreeCast ∘ bidegreeWeight isV) =
      bidegreeSign ∘ bidegreeWeight isV := by
  funext i
  cases hi : isV i <;>
    simp [operatorWeight, bidegreeWeight, bidegreeCast, bidegreeSign, hi]

/-- Differentiation by a polynomial of bidegree `(k,m)` lowers derivative degree
by `k` and raises multiplication degree by `m`. -/
theorem mixedOperator_mem_bidegreeSubmodule (isV : σ → Bool)
    {q p : MvPolynomial σ K} {k m a b : ℕ} (hka : k ≤ a)
    (hq : q ∈ bidegreeSubmodule isV k m)
    (hp : p ∈ bidegreeSubmodule isV a b) :
    mixedOperator isV q p ∈ bidegreeSubmodule isV (a - k) (b + m) := by
  have hq' := weighted_homogeneous_map bidegreeSign hq
  have hp' := weighted_homogeneous_map bidegreeCast hp
  rw [← operatorWeight_bidegree isV] at hq'
  have h := mixedOperator_isWeightedHomogeneous isV
    (bidegreeCast ∘ bidegreeWeight isV) hq' hp'
  intro e he
  apply bidegreeCast_injective
  rw [← weight_map_hom, h he]
  simp [bidegreeCast, bidegreeSign, Nat.cast_sub hka, sub_eq_add_neg]

/-- More differentiation than the available derivative degree annihilates the input. -/
theorem mixedOperator_eq_zero_of_bidegree_lt (isV : σ → Bool)
    {q p : MvPolynomial σ K} {k m a b : ℕ} (hka : a < k)
    (hq : q ∈ bidegreeSubmodule isV k m)
    (hp : p ∈ bidegreeSubmodule isV a b) : mixedOperator isV q p = 0 := by
  have hq' := weighted_homogeneous_map bidegreeSign hq
  have hp' := weighted_homogeneous_map bidegreeCast hp
  rw [← operatorWeight_bidegree isV] at hq'
  have h := mixedOperator_isWeightedHomogeneous isV
    (bidegreeCast ∘ bidegreeWeight isV) hq' hp'
  apply MvPolynomial.eq_zero_iff.mpr
  intro e
  by_contra he
  have he' := h he
  rw [weight_map_hom] at he'
  have hfst := congrArg Prod.fst he'
  simp [bidegreeCast, bidegreeSign] at hfst
  omega

/-- The degree-shift membership also holds without a degree inequality: when
`k > a`, the output is zero and belongs to every homogeneous submodule. -/
theorem mixedOperator_mem_bidegreeSubmodule_all (isV : σ → Bool)
    {q p : MvPolynomial σ K} {k m a b : ℕ}
    (hq : q ∈ bidegreeSubmodule isV k m)
    (hp : p ∈ bidegreeSubmodule isV a b) :
    mixedOperator isV q p ∈ bidegreeSubmodule isV (a - k) (b + m) := by
  by_cases hka : k ≤ a
  · exact mixedOperator_mem_bidegreeSubmodule isV hka hq hp
  · rw [mixedOperator_eq_zero_of_bidegree_lt isV (Nat.lt_of_not_ge hka) hq hp]
    exact Submodule.zero_mem _

end Problem335

end

end OAI
