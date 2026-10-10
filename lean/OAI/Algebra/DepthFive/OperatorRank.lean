import Mathlib

namespace OAI

/-!
Bigraded polynomial spaces used by the differentiation--multiplication rank measure.
The Boolean partition assigns derivative variables to `true` and multiplication
variables to `false`.
-/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*}

/-- Degree in derivative variables and in multiplication variables, respectively. -/
def bidegreeWeight (isV : σ → Bool) (i : σ) : ℕ × ℕ :=
  if isV i then (1, 0) else (0, 1)

@[simp] theorem bidegreeWeight_true (isV : σ → Bool) {i : σ} (hi : isV i = true) :
    bidegreeWeight isV i = (1, 0) := by simp [bidegreeWeight, hi]

@[simp] theorem bidegreeWeight_false (isV : σ → Bool) {i : σ} (hi : isV i = false) :
    bidegreeWeight isV i = (0, 1) := by simp [bidegreeWeight, hi]

/-- The sum of the two partial degrees is total degree. -/
theorem bidegreeWeight_total (isV : σ → Bool) (d : σ →₀ ℕ) :
    (Finsupp.weight (bidegreeWeight isV) d).1 +
      (Finsupp.weight (bidegreeWeight isV) d).2 = d.degree := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply,
    Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : isV i <;> simp [bidegreeWeight, h]

variable [CommSemiring K]

/-- The polynomial subspace of fixed bidegree. -/
def bidegreeSubmodule (isV : σ → Bool) (a b : ℕ) : Submodule K (MvPolynomial σ K) :=
  MvPolynomial.weightedHomogeneousSubmodule K (bidegreeWeight isV) (a, b)

/-- Linear projection to a fixed bidegree. -/
def bidegreeComponent (isV : σ → Bool) (a b : ℕ) :
    MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  MvPolynomial.weightedHomogeneousComponent (bidegreeWeight isV) (a, b)

@[simp] theorem mem_bidegreeSubmodule (isV : σ → Bool) (a b : ℕ)
    (p : MvPolynomial σ K) :
    p ∈ bidegreeSubmodule isV a b ↔
      p.IsWeightedHomogeneous (bidegreeWeight isV) (a, b) := Iff.rfl

@[simp] theorem coeff_bidegreeComponent (isV : σ → Bool) (a b : ℕ)
    (p : MvPolynomial σ K) (d : σ →₀ ℕ) :
    (bidegreeComponent isV a b p).coeff d =
      if Finsupp.weight (bidegreeWeight isV) d = (a, b)
      then p.coeff d else 0 :=
  MvPolynomial.coeff_weightedHomogeneousComponent _ _ _

 theorem bidegreeComponent_mem (isV : σ → Bool) (a b : ℕ)
    (p : MvPolynomial σ K) :
    bidegreeComponent isV a b p ∈ bidegreeSubmodule isV a b :=
  MvPolynomial.weightedHomogeneousComponent_mem _ _ _

 theorem bidegreeComponent_eq_self {isV : σ → Bool} {a b : ℕ}
    {p : MvPolynomial σ K} (hp : p ∈ bidegreeSubmodule isV a b) :
    bidegreeComponent isV a b p = p :=
  MvPolynomial.weightedHomogeneousComponent_eq_self hp

 theorem bidegreeSubmodule_isHomogeneous {isV : σ → Bool} {a b : ℕ}
    {p : MvPolynomial σ K} (hp : p ∈ bidegreeSubmodule isV a b) :
    p.IsHomogeneous (a + b) := by
  intro d hd
  have h := bidegreeWeight_total isV d
  rw [hp hd] at h
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h.symm

 theorem finite_bidegreeMonomials [Finite σ] (isV : σ → Bool) (a b : ℕ) :
    {d : σ →₀ ℕ | Finsupp.weight (bidegreeWeight isV) d = (a, b)}.Finite := by
  apply (Finsupp.finite_of_degree_le (σ := σ) (a + b)).subset
  intro d hd
  have h := bidegreeWeight_total isV d
  rw [hd] at h
  exact le_of_eq h.symm

instance bidegreeSubmodule_finite [Finite σ] (isV : σ → Bool) (a b : ℕ) :
    Module.Finite K (bidegreeSubmodule (K := K) isV a b) := by
  unfold bidegreeSubmodule
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_bidegreeMonomials isV a b).to_subtype
  exact Module.Finite.of_basis
    (MvPolynomial.basisRestrictSupport K
      {d | Finsupp.weight (bidegreeWeight isV) d = (a, b)})

 theorem bidegreeSubmodule_mul {isV : σ → Bool} {a b c d : ℕ}
    {p q : MvPolynomial σ K} (hp : p ∈ bidegreeSubmodule isV a b)
    (hq : q ∈ bidegreeSubmodule isV c d) :
    p * q ∈ bidegreeSubmodule isV (a + c) (b + d) :=
  hp.mul hq

 theorem bidegreeSubmodule_pderiv_true {isV : σ → Bool} {a b : ℕ} {i : σ}
    (hi : isV i = true) {p : MvPolynomial σ K}
    (hp : p ∈ bidegreeSubmodule isV a b) :
    MvPolynomial.pderiv i p ∈ bidegreeSubmodule isV (a - 1) b := by
  classical
  intro d hd
  rw [MvPolynomial.coeff_pderiv] at hd
  have h := hp (left_ne_zero_of_mul hd)
  simp only [map_add, Finsupp.weight_single, one_smul, bidegreeWeight_true isV hi] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext <;> dsimp at * <;> omega

 theorem bidegreeSubmodule_pderiv_false {isV : σ → Bool} {a b : ℕ} {i : σ}
    (hi : isV i = false) {p : MvPolynomial σ K}
    (hp : p ∈ bidegreeSubmodule isV a b) :
    MvPolynomial.pderiv i p ∈ bidegreeSubmodule isV a (b - 1) := by
  classical
  intro d hd
  rw [MvPolynomial.coeff_pderiv] at hd
  have h := hp (left_ne_zero_of_mul hd)
  simp only [map_add, Finsupp.weight_single, one_smul, bidegreeWeight_false isV hi] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext <;> dsimp at * <;> omega

 theorem bidegreeSubmodule_X_mul_true {isV : σ → Bool} {a b : ℕ} {i : σ}
    (hi : isV i = true) {p : MvPolynomial σ K}
    (hp : p ∈ bidegreeSubmodule isV a b) :
    MvPolynomial.X i * p ∈ bidegreeSubmodule isV (a + 1) b := by
  have hx := MvPolynomial.isWeightedHomogeneous_X (R := K) (bidegreeWeight isV) i
  rw [bidegreeWeight_true isV hi] at hx
  simpa only [mem_bidegreeSubmodule, Prod.mk_add_mk, Nat.add_comm 1, zero_add] using hx.mul hp

 theorem bidegreeSubmodule_X_mul_false {isV : σ → Bool} {a b : ℕ} {i : σ}
    (hi : isV i = false) {p : MvPolynomial σ K}
    (hp : p ∈ bidegreeSubmodule isV a b) :
    MvPolynomial.X i * p ∈ bidegreeSubmodule isV a (b + 1) := by
  have hx := MvPolynomial.isWeightedHomogeneous_X (R := K) (bidegreeWeight isV) i
  rw [bidegreeWeight_false isV hi] at hx
  simpa only [mem_bidegreeSubmodule, Prod.mk_add_mk, Nat.add_comm 1, zero_add] using hx.mul hp

/-- A homogeneous polynomial splits into its finitely many possible bidegrees. -/
theorem bidegree_decomposition (isV : σ → Bool) {n : ℕ}
    {p : MvPolynomial σ K} (hp : p.IsHomogeneous n) :
    p = ∑ i : Fin (n + 1), bidegreeComponent isV i (n - i) p := by
  classical
  ext d
  rw [MvPolynomial.coeff_sum]
  by_cases hd : p.coeff d = 0
  · simp [coeff_bidegreeComponent, hd]
  have hn : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp hd
  have ht := bidegreeWeight_total isV d
  rw [hn] at ht
  let i : Fin (n + 1) := ⟨(Finsupp.weight (bidegreeWeight isV) d).1, by omega⟩
  symm
  rw [Finset.sum_eq_single i]
  · rw [coeff_bidegreeComponent, ite_eq_left]
    apply Prod.ext
    · rfl
    · dsimp [i]
      omega
  · intro j hj hji
    rw [coeff_bidegreeComponent, ite_eq_right]
    intro heq
    apply hji
    apply Fin.ext
    exact (congrArg Prod.fst heq).symm
  · simp

/-- Projection acts diagonally on a polynomial already of a fixed bidegree. -/
theorem bidegreeComponent_of_mem {isV : σ → Bool} {a b k m : ℕ}
    {p : MvPolynomial σ K} (hp : p ∈ bidegreeSubmodule isV a b) :
    bidegreeComponent isV k m p = if k = a ∧ m = b then p else 0 := by
  simpa only [bidegreeComponent, Prod.mk.injEq] using
    MvPolynomial.weightedHomogeneousComponent_of_mem (w := bidegreeWeight isV)
      (m := (k, m)) hp

/-- Finite products add both partial degrees. -/
theorem bidegreeSubmodule_prod {ι : Type*} (s : Finset ι)
    {isV : σ → Bool} {a b : ι → ℕ} {p : ι → MvPolynomial σ K}
    (hp : ∀ j ∈ s, p j ∈ bidegreeSubmodule isV (a j) (b j)) :
    (∏ j ∈ s, p j) ∈ bidegreeSubmodule isV (∑ j ∈ s, a j) (∑ j ∈ s, b j) := by
  have hs : (∑ j ∈ s, (a j, b j)) = (∑ j ∈ s, a j, ∑ j ∈ s, b j) := by
    ext <;> simp only [Prod.fst_sum, Prod.snd_sum]
  rw [mem_bidegreeSubmodule, ← hs]
  exact MvPolynomial.IsWeightedHomogeneous.prod s p (fun j => (a j, b j)) hp

/-- Expansion of a product into all choices of factor bidegrees. -/
theorem product_bidegree_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (isV : σ → Bool) (e : ι → ℕ) (p : ι → MvPolynomial σ K)
    (hp : ∀ j, (p j).IsHomogeneous (e j)) :
    (∏ j, p j) = ∑ a : (∀ j : ι, Fin (e j + 1)),
      ∏ j, bidegreeComponent isV (a j) (e j - a j) (p j) := by
  classical
  calc
    (∏ j, p j) = ∏ j, ∑ a : Fin (e j + 1),
        bidegreeComponent isV a (e j - a) (p j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact bidegree_decomposition isV (hp j)
    _ = _ := Fintype.prod_sum _

/-- The fixed-bidegree component of a product is the constrained assignment sum. -/
theorem bidegreeComponent_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (isV : σ → Bool) (e : ι → ℕ) (p : ι → MvPolynomial σ K)
    (hp : ∀ j, (p j).IsHomogeneous (e j)) (k m : ℕ) :
    bidegreeComponent isV k m (∏ j, p j) =
      ∑ a : (∀ j : ι, Fin (e j + 1)),
        if (∑ j : ι, (a j : ℕ)) = k ∧ (∑ j : ι, (e j - (a j : ℕ))) = m then
          ∏ j, bidegreeComponent isV (a j) (e j - a j) (p j)
        else 0 := by
  classical
  rw [product_bidegree_decomposition isV e p hp, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have h := bidegreeSubmodule_prod (Finset.univ : Finset ι)
    (fun j _ => bidegreeComponent_mem isV (a j) (e j - a j) (p j))
  rw [bidegreeComponent_of_mem h]
  simp only [eq_comm]

end Problem335

end

end OAI
