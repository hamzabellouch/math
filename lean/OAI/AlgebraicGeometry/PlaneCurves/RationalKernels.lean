import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

namespace OAI

/-!
# Rational polynomial kernels and normalization without cancellation
-/

section

/-!
# Noncancellation in the lowest normal weight
-/

namespace Nagata.W18

open scoped BigOperators

/-- On a fixed diagonal `α + j α = u`, the normal exponent determines `α`. -/
theorem exponent_injective_on_diagonal (s : Finset ℕ) (j : ℕ → ℕ) (u : ℕ)
    (hweight : ∀ a ∈ s, a + j a = u) :
    Set.InjOn j (↑s : Set ℕ) := by
  intro a ha b hb hab
  apply @Nat.add_right_cancel a (j a) b
  calc
    a + j a = u := hweight a ha
    _ = b + j b := (hweight b hb).symm
    _ = b + j a := congrArg (fun n => b + n) hab.symm

/-- A sum of monomials with distinct exponents retains each selected coefficient. -/
theorem coefficient_of_injective_monomial_sum {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hinj : Set.InjOn j (↑s : Set ℕ)) (a : ℕ) (ha : a ∈ s) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)).coeff (j a) = c a := by
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single a]
  · exact Polynomial.coeff_monomial_same _ _
  · intro b hb hba
    apply Polynomial.coeff_monomial_of_ne
    intro hab
    exact hba (hinj hb ha hab.symm)
  · intro h
    exact (h ha).elim

/-- One nonzero coefficient suffices for noncancellation when exponents are distinct. -/
theorem injective_monomial_sum_ne_zero {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hinj : Set.InjOn j (↑s : Set ℕ))
    (hcoeff : ∃ a ∈ s, c a ≠ 0) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha, hca⟩ := hcoeff
  intro hz
  apply hca
  calc
    c a = (∑ b ∈ s, Polynomial.monomial (j b) (c b)).coeff (j a) :=
      (coefficient_of_injective_monomial_sum s j c hinj a ha).symm
    _ = 0 := by rw [hz, Polynomial.coeff_zero]

/-- The exact finite noncancellation step used after choosing the minimum weight. -/
theorem diagonal_monomial_sum_ne_zero {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R) (u : ℕ)
    (hweight : ∀ a ∈ s, a + j a = u)
    (hne : s.Nonempty) (hcoeff : ∀ a ∈ s, c a ≠ 0) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha⟩ := hne
  exact injective_monomial_sum_ne_zero s j c
    (exponent_injective_on_diagonal s j u hweight) ⟨a, ha, hcoeff a ha⟩

/-- A finite nonzero family has a nonzero lowest-weight polynomial.

The construction also records the inequality needed to make every exponent of
` s ` in the divided family nonnegative. This is finite algebra only.
-/
theorem exists_lowest_weight_polynomial {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hne : s.Nonempty) (hcoeff : ∀ a ∈ s, c a ≠ 0) :
    ∃ u : ℕ,
      (∀ a ∈ s, u ≤ a + j a) ∧
      (s.filter (fun a => a + j a = u)).Nonempty ∧
      (∑ b ∈ s.filter (fun a => a + j a = u),
        Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image (fun b => b + j b) hne
  let u := a + j a
  have hselected : (s.filter (fun b => b + j b = u)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  refine ⟨u, hmin, hselected, ?_⟩
  apply diagonal_monomial_sum_ne_zero _ j c u
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · exact hselected
  · intro b hb
    exact hcoeff b (Finset.mem_filter.mp hb).1

end Nagata.W18

end

section

/-!
# Removing the maximal common parameter power

For an actual polynomial coefficient vector, extract a common power of `X`
until its specialization at zero is nonzero. Kernel equations are preserved
by cancellation in the polynomial domain. This is the normalization step
before the manuscript writes `S(s)=Σ s^α S_α` with `S₀≠0`.
-/

noncomputable section

namespace Nagata.W18

/-- A nonzero polynomial vector has a least parameter degree occurring in any
coordinate, even when the index type is not assumed finite. -/
theorem normalize_parameter_vector {K ι : Type*} [Field K]
    (p : ι → Polynomial K) (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ q : ι → Polynomial K,
      (∀ i, p i = Polynomial.X ^ n * q i) ∧
      ∃ i, (q i).coeff 0 ≠ 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ i, (p i).coeff n ≠ 0 := by
    by_contra h
    apply hp
    funext i
    apply Polynomial.ext
    intro n
    have hn : (p i).coeff n = 0 := by
      by_contra hn
      exact h ⟨n, i, hn⟩
    simpa only [Pi.zero_apply, Polynomial.coeff_zero] using hn
  let n := Nat.find hex
  have hsmall : ∀ k < n, ∀ i, (p i).coeff k = 0 := by
    intro k hk i
    by_contra hki
    exact (Nat.find_min hex hk) ⟨i, hki⟩
  have hdiv : ∀ i, Polynomial.X ^ n ∣ p i := by
    intro i
    exact Polynomial.X_pow_dvd_iff.mpr (fun k hk => hsmall k hk i)
  choose q hq using hdiv
  refine ⟨n, q, hq, ?_⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  refine ⟨i, ?_⟩
  intro hzero
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hzero
  have hdivsucc : Polynomial.X ^ (n + 1) ∣ p i := by
    refine ⟨r, ?_⟩
    rw [hq i, hr, pow_succ, mul_assoc]
  exact hi (Polynomial.X_pow_dvd_iff.mp hdivsucc n (Nat.lt_succ_self n))

/-- Removing a common parameter power preserves every polynomial matrix kernel
equation and leaves a vector whose value at zero is nonzero. -/
theorem normalize_parameter_kernel {K ι κ : Type*} [Field K] [Fintype ι]
    (A : Matrix κ ι (Polynomial K)) (p : ι → Polynomial K)
    (hp : p ≠ 0) (hAp : A.mulVec p = 0) :
    ∃ n : ℕ, ∃ q : ι → Polynomial K,
      (∀ i, p i = Polynomial.X ^ n * q i) ∧
      (∃ i, (q i).coeff 0 ≠ 0) ∧ A.mulVec q = 0 := by
  obtain ⟨n, q, hq, hqzero⟩ := normalize_parameter_vector p hp
  refine ⟨n, q, hq, hqzero, ?_⟩
  have hpeq : p = (Polynomial.X : Polynomial K) ^ n • q := by
    funext i
    exact hq i
  rw [hpeq, Matrix.mulVec_smul] at hAp
  funext k
  exact (mul_eq_zero.mp (congrFun hAp k)).resolve_left
    (pow_ne_zero n Polynomial.X_ne_zero)

/-- The nonzero constant coefficient is exactly nonzero specialization at zero. -/
theorem specialization_zero_ne_zero {K ι : Type*} [Field K]
    (q : ι → Polynomial K) (hq : ∃ i, (q i).coeff 0 ≠ 0) :
    (fun i => (q i).eval 0) ≠ 0 := by
  obtain ⟨i, hi⟩ := hq
  intro hz
  apply hi
  have h := congrFun hz i
  simpa only [Polynomial.coeff_zero_eq_eval_zero, Pi.zero_apply] using h

end Nagata.W18

end
end

section

/-!
# A polynomial kernel from kernels at general parameter values
-/

noncomputable section
open scoped BigOperators

namespace Nagata.W18

/-- A finite family in a fraction field has a common nonzero denominator. -/
theorem clear_finite_denominators {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [Finite ι] (v : ι → FractionRing R) :
    ∃ d : R, d ≠ 0 ∧ ∃ p : ι → R,
      ∀ i, algebraMap R (FractionRing R) (p i) =
        algebraMap R (FractionRing R) d * v i := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) v
  choose p hp using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, p, ?_⟩
  intro i
  simpa only [Algebra.smul_def] using hp i

/-- Mapping a scalar identity matrix maps only its scalar. -/
theorem map_scalar_identity {R K : Type*} [CommRing R] [CommRing K]
    {ι : Type*} [DecidableEq ι] (f : R →+* K) (d : R) :
    (d • (1 : Matrix ι ι R)).map f = f d • (1 : Matrix ι ι K) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, h, smul_eq_mul]

/-- An injective fraction-field matrix has a polynomial left inverse up to a
single nonzero scalar. This is an actual denominator-cleared identity. -/
theorem polynomial_scaled_left_inverse {R : Type*} [CommRing R] [IsDomain R]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι R)
    (hinj : Function.Injective (A.map (algebraMap R (FractionRing R))).mulVec) :
    ∃ d : R, d ≠ 0 ∧ ∃ D : Matrix ι κ R, D * A = d • (1 : Matrix ι ι R) := by
  classical
  let f := algebraMap R (FractionRing R)
  obtain ⟨g, hg⟩ := (Matrix.toLin' (A.map f)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let C := LinearMap.toMatrix' g
  have hC : C * A.map f = 1 := by
    simpa only [C, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  obtain ⟨d, hd, p, hp⟩ := clear_finite_denominators (fun z : ι × κ => C z.1 z.2)
  let D : Matrix ι κ R := fun i k => p (i, k)
  have hD : D.map f = f d • C := by
    ext i k
    exact hp (i, k)
  refine ⟨d, hd, D, ?_⟩
  apply Matrix.map_injective (IsFractionRing.injective R (FractionRing R))
  change (D * A).map f = (d • (1 : Matrix ι ι R)).map f
  rw [Matrix.map_mul, hD, Matrix.smul_mul, hC, map_scalar_identity]

/-- Clearing a nonzero fraction-field kernel preserves nonzeroness and
produces an actual kernel vector over the original domain. -/
theorem clear_fraction_kernel {R : Type*} [CommRing R] [IsDomain R]
    {ι κ : Type*} [Fintype ι] (A : Matrix κ ι R)
    (v : ι → FractionRing R) (hv : v ≠ 0)
    (hAv : (A.map (algebraMap R (FractionRing R))).mulVec v = 0) :
    ∃ p : ι → R, p ≠ 0 ∧ A.mulVec p = 0 := by
  classical
  let f := algebraMap R (FractionRing R)
  obtain ⟨d, hd, p, hp⟩ := clear_finite_denominators v
  have hfd : f d ≠ 0 := by
    intro hz
    exact hd (IsFractionRing.injective R (FractionRing R) (by simpa [f] using hz))
  have hmap : f ∘ p = f d • v := by
    funext i
    exact hp i
  refine ⟨p, ?_, ?_⟩
  · intro hpzero
    apply hv
    funext i
    have hi : f d * v i = 0 := by
      rw [← hp i, hpzero]
      exact map_zero f
    exact (mul_eq_zero.mp hi).resolve_left hfd
  · funext k
    apply IsFractionRing.injective R (FractionRing R)
    change f ((A.mulVec p) k) = f 0
    rw [RingHom.map_mulVec, hmap, Matrix.mulVec_smul, hAv]
    simp

/-- Polynomial kernel identities specialize at every parameter value. -/
theorem specialize_polynomial_kernel {K ι κ : Type*} [Field K] [Fintype ι]
    (A : Matrix κ ι (Polynomial K)) (p : ι → Polynomial K)
    (hp : A.mulVec p = 0) (s : K) :
    (A.map (Polynomial.evalRingHom s)).mulVec (fun i => (p i).eval s) = 0 := by
  funext k
  have h := RingHom.map_mulVec (Polynomial.evalRingHom s) A p k
  rw [hp] at h
  simpa only [Pi.zero_apply, map_zero, Polynomial.coe_evalRingHom,
    Function.comp_def] using h.symm

/-- A polynomial nonzero scalar cannot vanish at every parameter outside a
finite exceptional set. -/
theorem exists_parameter_avoiding_roots {K : Type*} [Field K] [Infinite K]
    (E : Finset K) (d : Polynomial K) (hd : d ≠ 0) :
    ∃ s : K, s ∉ E ∧ d.eval s ≠ 0 := by
  obtain ⟨s, hs⟩ := (E.finite_toSet.union (Polynomial.finite_setOfPred_isRoot hd)).exists_notMem
  exact ⟨s, fun h => hs (Or.inl h), fun h => hs (Or.inr h)⟩

/-- General specialized kernels force a kernel over the rational function field. -/
theorem rational_kernel_of_general_specialized_kernel
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ v : ι → FractionRing (Polynomial K), v ≠ 0 ∧
      (A.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).mulVec v = 0 := by
  classical
  by_contra hnone
  have hinj : Function.Injective
      (A.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).mulVec := by
    have hker : LinearMap.ker
        (Matrix.mulVecLin (A.map (algebraMap (Polynomial K)
          (FractionRing (Polynomial K))))) = ⊥ := by
      apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
      intro v hv
      by_contra hne
      exact hnone ⟨v, hne, hv⟩
    exact LinearMap.ker_eq_bot.mp hker
  obtain ⟨d, hd, D, hDA⟩ := polynomial_scaled_left_inverse A hinj
  obtain ⟨s, hsE, hds⟩ := exists_parameter_avoiding_roots E d hd
  obtain ⟨v, hv, hAv⟩ := hkernel s hsE
  let ev := Polynomial.evalRingHom s
  have hDAeval : D.map ev * A.map ev = d.eval s • (1 : Matrix ι ι K) := by
    have h := congrArg (fun M : Matrix ι ι (Polynomial K) => M.map ev) hDA
    change (D * A).map ev = (d • (1 : Matrix ι ι (Polynomial K))).map ev at h
    rw [Matrix.map_mul (f := ev), map_scalar_identity] at h
    exact h
  have hscalar : d.eval s • v = 0 := by
    calc
      d.eval s • v = (d.eval s • (1 : Matrix ι ι K)).mulVec v := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (D.map ev * A.map ev).mulVec v := by rw [hDAeval]
      _ = (D.map ev).mulVec ((A.map ev).mulVec v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hAv, Matrix.mulVec_zero]
  apply hv
  funext i
  exact (mul_eq_zero.mp (congrFun hscalar i)).resolve_left hds

/-- The complete algebraic family step: kernels at all general parameters
supply a nonzero polynomial family of coefficient vectors in the kernel. -/
theorem polynomial_kernel_of_general_specialized_kernel
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ p : ι → Polynomial K, p ≠ 0 ∧ A.mulVec p = 0 := by
  obtain ⟨v, hv, hAv⟩ := rational_kernel_of_general_specialized_kernel A E hkernel
  exact clear_fraction_kernel A v hv hAv

end Nagata.W18

end
end

section

namespace Nagata.W18

/-- The manuscript's algebraic family conclusion, including nonzero constant
coefficient, follows from nonzero kernels at all general parameters. -/
theorem normalized_kernel_of_general_specialized_kernel
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ q : ι → Polynomial K, (∃ i, (q i).coeff 0 ≠ 0) ∧ A.mulVec q = 0 := by
  obtain ⟨p, hp, hAp⟩ := polynomial_kernel_of_general_specialized_kernel A E hkernel
  obtain ⟨n, q, _, hqzero, hAq⟩ := normalize_parameter_kernel A p hp hAp
  exact ⟨q, hqzero, hAq⟩

end Nagata.W18

end

end OAI
