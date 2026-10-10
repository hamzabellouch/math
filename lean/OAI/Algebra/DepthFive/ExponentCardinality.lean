import OAI.Algebra.DepthFive.OperatorRank

namespace OAI

/-! # Cardinalities of homogeneous and bihomogeneous exponent sets -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ : Type*}

/-- Stars and bars for finitely supported natural exponent vectors. -/
theorem card_homogeneous_exponents (σ : Type*) [Fintype σ] (a : ℕ) :
    Nat.card {d : σ →₀ ℕ // d.sum (fun _ n => n) = a} =
      (Fintype.card σ).multichoose a := by
  classical
  change Nat.card {d : σ →₀ ℕ // d.sum (fun _ => id) = a} = _
  rw [← Nat.card_congr (Sym.equivNatSum σ a), Nat.card_eq_fintype_card]
  exact Sym.card_sym_eq_multichoose σ a

/-- Stars and bars for ordinary natural exponent vectors on a finite type. -/
theorem card_homogeneous_functions (σ : Type*) [Fintype σ] (a : ℕ) :
    Nat.card {d : σ → ℕ // ∑ x, d x = a} =
      (Fintype.card σ).multichoose a := by
  classical
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype σ a), Nat.card_eq_fintype_card]
  exact Sym.card_sym_eq_multichoose σ a

lemma bidegreeWeight_fst_sum [Fintype σ] (isV : σ → Bool) (d : σ →₀ ℕ) :
    (Finsupp.weight (bidegreeWeight isV) d).1 =
      ∑ x : {x // isV x = true}, d x := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Prod.fst_sum]
  calc
    _ = ∑ x, if isV x = true then d x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      cases h : isV x <;> simp [bidegreeWeight, h]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

lemma bidegreeWeight_snd_sum [Fintype σ] (isV : σ → Bool) (d : σ →₀ ℕ) :
    (Finsupp.weight (bidegreeWeight isV) d).2 =
      ∑ x : {x // ¬ isV x = true}, d x := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Prod.snd_sum]
  calc
    _ = ∑ x, if ¬ isV x = true then d x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      cases h : isV x <;> simp [bidegreeWeight, h]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

/-- Split a bihomogeneous monomial into its two independent exponent vectors. -/
def bidegreeExponentsEquiv [Fintype σ] (isV : σ → Bool) (a b : ℕ) :
    {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)} ≃
      {d : {x // isV x = true} → ℕ // ∑ x, d x = a} ×
      {d : {x // ¬ isV x = true} → ℕ // ∑ x, d x = b} := by
  classical
  let e : (σ →₀ ℕ) ≃
      ({x // isV x = true} → ℕ) × ({x // ¬ isV x = true} → ℕ) :=
    Finsupp.equivFunOnFinite.trans
      (Equiv.piEquivPiSubtypeProd (fun x => isV x = true) (fun _ => ℕ))
  refine (e.subtypeEquiv (q := fun z => (∑ x, z.1 x) = a ∧ (∑ x, z.2 x) = b)
    ?_).trans (Equiv.subtypeProdEquivProd
      (p := fun d : {x // isV x = true} → ℕ => (∑ x, d x) = a)
      (q := fun d : {x // ¬ isV x = true} → ℕ => (∑ x, d x) = b))
  intro d
  change Finsupp.weight (bidegreeWeight isV) d = (a, b) ↔
    (∑ x : {x // isV x = true}, d x) = a ∧
      (∑ x : {x // ¬ isV x = true}, d x) = b
  rw [Prod.ext_iff, bidegreeWeight_fst_sum, bidegreeWeight_snd_sum]

/-- Bihomogeneous monomials are counted by the product of two stars-and-bars
numbers; the variable sets may be empty. -/
theorem card_bidegree_exponents [Fintype σ] (isV : σ → Bool) (a b : ℕ) :
    Nat.card {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)} =
      (Fintype.card {x // isV x = true}).multichoose a *
        (Fintype.card {x // ¬ isV x = true}).multichoose b := by
  classical
  rw [Nat.card_congr (bidegreeExponentsEquiv isV a b), Nat.card_prod,
    card_homogeneous_functions, card_homogeneous_functions]

/-- The same count with the explicit `false` Boolean fiber. -/
theorem card_bidegree_exponents_bool [Fintype σ] (isV : σ → Bool) (a b : ℕ) :
    Nat.card {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)} =
      (Fintype.card {x // isV x = true}).multichoose a *
        (Fintype.card {x // isV x = false}).multichoose b := by
  simpa only [Bool.not_eq_true] using card_bidegree_exponents isV a b

/-- Each selected matrix layer contributes all `n²` ambient variables. -/
theorem card_layer_variables {n : ℕ} (s : Finset (Fin n)) :
    Fintype.card {x : Fin n × Fin n × Fin n // x.1 ∈ s} = s.card * n ^ 2 := by
  classical
  rw [Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd
    (α := Fin n) (β := Fin n × Fin n) (p := fun x => x ∈ s))]
  simp [pow_two]

/-- The complementary group has the expected number of ambient variables. -/
theorem card_complement_layer_variables {n : ℕ} (s : Finset (Fin n)) :
    Fintype.card {x : Fin n × Fin n × Fin n // x.1 ∉ s} =
      (n - s.card) * n ^ 2 := by
  classical
  simpa only [Finset.mem_compl, Finset.card_compl, Fintype.card_fin] using card_layer_variables sᶜ

/-- The exact dimension index count for a partition by complete matrix layers.
In particular, inactive endpoint coordinates remain part of both stars-and-bars
counts, as required in the occupation-moment argument. -/
theorem card_layer_bidegree_exponents {n : ℕ} (s : Finset (Fin n)) (a b : ℕ) :
    Nat.card {d : (Fin n × Fin n × Fin n) →₀ ℕ //
      Finsupp.weight (bidegreeWeight (fun x => decide (x.1 ∈ s))) d = (a, b)} =
      (s.card * n ^ 2).multichoose a *
        ((n - s.card) * n ^ 2).multichoose b := by
  classical
  simpa only [decide_eq_true_eq, card_layer_variables,
    card_complement_layer_variables] using
      card_bidegree_exponents (fun x : Fin n × Fin n × Fin n => decide (x.1 ∈ s)) a b

/-- An explicit finite enumeration for a weak-composition function type.  This
is not installed globally, so consumers may choose their preferred enumeration. -/
abbrev homogeneousFunctionsFintype (σ : Type*) [Fintype σ] (a : ℕ) :
    Fintype {d : σ → ℕ // ∑ x, d x = a} := by
  classical
  exact Fintype.ofEquiv (Sym σ a) (Sym.equivNatSumOfFintype σ a)

/-- The weak-composition function representation and the finite antidiagonal
representation used by power-series coefficient extraction are equivalent. -/
def homogeneousFunctionsEquivAntidiag [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {d : σ → ℕ // ∑ x, d x = a} ≃
      ↥(Finset.finsuppAntidiag (Finset.univ : Finset σ) a) := by
  classical
  refine Finsupp.equivFunOnFinite.symm.subtypeEquiv ?_
  intro d
  simp [Finset.mem_finsuppAntidiag]

/-- Exact transport of a weak-composition sum to the finite antidiagonal. -/
theorem sum_homogeneousFunctions_eq_antidiag [Fintype σ] [DecidableEq σ] (a : ℕ)
    [Fintype {d : σ → ℕ // ∑ x, d x = a}]
    {M : Type*} [AddCommMonoid M] (f : (σ →₀ ℕ) → M) :
    (∑ d : {d : σ → ℕ // ∑ x, d x = a},
      f (Finsupp.equivFunOnFinite.symm d.val)) =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) a, f d := by
  classical
  calc
    _ = ∑ d : ↥(Finset.finsuppAntidiag (Finset.univ : Finset σ) a), f d :=
      (homogeneousFunctionsEquivAntidiag a).sum_comp (fun d => f d.val)
    _ = _ := Finset.sum_coe_sort _ _

end Problem335

end

end OAI
