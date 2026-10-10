import OAI.Combinatorics.CompleteCrossing.Interpolation
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic
import Mathlib.Tactic.NormNum

namespace OAI

/-! Coordinate symmetry, polynomial quotients, collision divisibility, and specialization. -/

section

noncomputable section
open MvPolynomial
namespace Paper170

lemma substitution_difference_dvd {σ : Type*} (f : MvPolynomial σ ℝ)
    (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ)
    (hX : ∀ i, f ∣ X i - φ (X i)) (P : MvPolynomial σ ℝ) : f ∣ P - φ P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
    have h := dvd_add hP hQ
    simpa only [map_add, sub_add_sub_comm] using h
  | mul_X P i hP =>
    have h := dvd_add (dvd_mul_of_dvd_left hP (X i))
      (dvd_mul_of_dvd_right (hX i) (φ P))
    convert h using 1
    rw [map_mul]
    ring

private def reinsertDiagonal : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] Poly4 :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 3]

theorem diagonal_vanishing_iff_divisible (P : Poly4) :
    diagonalSpecialization P = 0 ↔ (X 0 - X 2 : Poly4) ∣ P := by
  let φ : Poly4 →ₐ[ℝ] Poly4 := reinsertDiagonal.comp diagonalSpecialization
  have hX : ∀ i, (X 0 - X 2 : Poly4) ∣ X i - φ (X i) := by
    intro i
    fin_cases i <;> simp [φ, reinsertDiagonal, diagonalSpecialization,
      Matrix.cons_val_two, Matrix.cons_val_three]
    exact ⟨-1, by ring⟩
  constructor
  · intro hP
    have h := substitution_difference_dvd (X 0 - X 2) φ hX P
    simpa [φ, hP] using h
  · rintro ⟨Q, rfl⟩
    simp [diagonalSpecialization, Matrix.cons_val_two]

end Paper170

end
end

section

noncomputable section
open MvPolynomial
namespace Paper170

lemma difference_coefficient (i j : Fin 4) (hij : i ≠ j) :
    (X i - X j : Poly4).coeff (Finsupp.single i 1) = 1 := by
  simp [coeff_X, Finsupp.single_left_inj, Ne.symm hij]

lemma difference_degree (i j : Fin 4) (hij : i ≠ j) (k : Fin 4) :
    (X i - X j : Poly4).degreeOf k = if k = i ∨ k = j then 1 else 0 := by
  have hupper := degreeOf_sub_le k (X i : Poly4) (X j)
  simp only [degreeOf_X] at hupper
  by_cases hki : k = i
  · subst k
    rw [ite_eq_left (Or.inl rfl)]
    apply Nat.le_antisymm
    · simpa [hij] using hupper
    · have hm : Finsupp.single i 1 ∈ (X i - X j : Poly4).support :=
        mem_support_iff.mpr (by rw [difference_coefficient i j hij]; norm_num)
      simpa using monomial_le_degreeOf i hm
  · by_cases hkj : k = j
    · subst k
      rw [ite_eq_left (Or.inr rfl)]
      apply Nat.le_antisymm
      · simpa [hki] using hupper
      · have hc : (X i - X j : Poly4).coeff (Finsupp.single j 1) = -1 := by
          simp [coeff_X, Finsupp.single_left_inj, hij]
        have hm : Finsupp.single j 1 ∈ (X i - X j : Poly4).support :=
          mem_support_iff.mpr (by rw [hc]; norm_num)
        simpa using monomial_le_degreeOf j hm
    · rw [ite_eq_right (not_or.mpr ⟨hki, hkj⟩)]
      exact Nat.eq_zero_of_le_zero (by simpa [hki, hkj] using hupper)

theorem difference_prime (i j : Fin 4) (hij : i ≠ j) :
    Prime (X i - X j : Poly4) := by
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  apply irreducible_of_totalDegree_eq_one
  · apply Nat.le_antisymm
    · simpa using totalDegree_sub (X i : Poly4) (X j)
    · have h := degreeOf_le_totalDegree (X i - X j : Poly4) i
      simpa [difference_degree i j hij] using h
  · intro r hr
    apply isUnit_of_dvd_one
    simpa only [difference_coefficient i j hij] using hr (Finsupp.single i 1)

theorem collision_factors_nonassociate :
    Pairwise (fun i j : Fin 4 => ¬ Associated (collisionFactors i) (collisionFactors j)) := by
  let w : Fin 4 → Fin 4 → ℝ := ![![0, 1, 0, 2], ![0, 1, 2, 0],
    ![1, 0, 0, 2], ![1, 0, 2, 0]]
  intro i j hij ha
  have hi : eval (w i) (collisionFactors i) = 0 := by
    fin_cases i <;> norm_num [w, collisionFactors, Matrix.cons_val_two, Matrix.cons_val_three]
  have hj : eval (w i) (collisionFactors j) ≠ 0 := by
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | norm_num [w, collisionFactors,
      Matrix.cons_val_two, Matrix.cons_val_three]
  obtain ⟨Q, hQ⟩ := ha.dvd
  have h := congrArg (eval (w i)) hQ
  simp only [eval_mul, hi, zero_mul] at h
  exact hj h

theorem collision_factor_properties :
    collisionFactor ≠ 0 ∧ swapFirstPair collisionFactor = collisionFactor ∧
      swapSecondPair collisionFactor = collisionFactor ∧
      ∀ i : Fin 4, collisionFactor.degreeOf i = 2 := by
  have h02 := (difference_prime 0 2 (by decide)).ne_zero
  have h03 := (difference_prime 0 3 (by decide)).ne_zero
  have h12 := (difference_prime 1 2 (by decide)).ne_zero
  have h13 := (difference_prime 1 3 (by decide)).ne_zero
  refine ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero h02 h03) h12) h13, ?_, ?_, ?_⟩
  · norm_num [collisionFactor, swapFirstPair, Equiv.swap_apply_def, Fin.ext_iff]
    ring
  · norm_num [collisionFactor, swapSecondPair, Equiv.swap_apply_def, Fin.ext_iff]
    ring
  · intro i
    rw [collisionFactor, degreeOf_mul_eq (mul_ne_zero (mul_ne_zero h02 h03) h12) h13,
      degreeOf_mul_eq (mul_ne_zero h02 h03) h12, degreeOf_mul_eq h02 h03]
    fin_cases i <;> norm_num [difference_degree, Fin.ext_iff, show (0 : Fin 4) ≠ 2 by decide,
      show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 2 by decide,
      show (1 : Fin 4) ≠ 3 by decide]

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open Module MvPolynomial
namespace Paper170

abbrev BoundedExponents (d : ℕ) := Fin 4 → Fin (d + 1)

def tupleExponent {d : ℕ} (t : BoundedExponents d) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (t i).val)

@[simp] lemma tupleExponent_apply {d : ℕ} (t : BoundedExponents d) (i : Fin 4) :
    tupleExponent t i = (t i).val := rfl

def boxExponentEquiv (d : ℕ) :
    {m : Fin 4 →₀ ℕ // ∀ i, m i ≤ d} ≃ BoundedExponents d where
  toFun m i := ⟨m.val i, Nat.lt_succ_of_le (m.property i)⟩
  invFun t := ⟨tupleExponent t, fun i => Nat.le_of_lt_succ (t i).isLt⟩
  left_inv m := by apply Subtype.ext; ext i; rfl
  right_inv t := rfl

lemma box_eq_restrictSupport (d : ℕ) :
    box4 d = MvPolynomial.restrictSupport ℝ {m | ∀ i, m i ≤ d} := by
  ext P
  rw [box4_membership, MvPolynomial.mem_restrictSupport_iff]
  simp only [degreeOf_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]
  exact ⟨fun h m hm i => h i m hm, fun h i m hm => h m hm i⟩

def boxBasis (d : ℕ) : Basis (BoundedExponents d) ℝ (box4 d) :=
  ((MvPolynomial.basisRestrictSupport ℝ _).reindex (boxExponentEquiv d)).map
    (LinearEquiv.ofEq _ _ (box_eq_restrictSupport d).symm)

lemma box_finite (d : ℕ) : FiniteDimensional ℝ (box4 d) :=
  Module.Finite.of_basis (boxBasis d)

@[simp] lemma boxBasis_repr (d : ℕ) (P : box4 d) (t : BoundedExponents d) :
    (boxBasis d).repr P t = P.val.coeff (tupleExponent t) := by
  rfl

theorem symmetric_space_finite (s : ℕ) :
    FiniteDimensional ℝ (endpointSymmetricSpace s) := by
  let := box_finite (s - 2)
  let f : endpointSymmetricSpace s →ₗ[ℝ] box4 (s - 2) :=
    Submodule.inclusion (inf_le_left.trans inf_le_left)
  exact FiniteDimensional.of_injective f (Submodule.inclusion_injective _)

end Paper170

end
end

section

noncomputable section
namespace Paper170

@[simp] lemma swapFirstPair_mul (P Q : Poly4) :
    swapFirstPair (P * Q) = swapFirstPair P * swapFirstPair Q := by
  exact map_mul (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1)) P Q

@[simp] lemma swapSecondPair_mul (P Q : Poly4) :
    swapSecondPair (P * Q) = swapSecondPair P * swapSecondPair Q := by
  exact map_mul (MvPolynomial.rename (Equiv.swap (2 : Fin 4) 3)) P Q

theorem collision_quotient (s : ℕ) (_hs : 2 ≤ s) (P : Poly4)
    (hP : P ∈ endpointSymmetricSpace s) (hP0 : P ≠ 0) (hdiv : collisionFactor ∣ P) :
    ∃ Q : Poly4, Q ≠ 0 ∧ P = collisionFactor * Q ∧
      Q ∈ endpointSymmetricSpace s ∧
      (∀ i : Fin 4, Q.degreeOf i + 2 = P.degreeOf i) ∧
      Q.degreeOf 0 < P.degreeOf 0 := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hP0
    simp [h, hQ]
  rcases collision_factor_properties with ⟨hc, hc1, hc2, hcd⟩
  rcases (symmetric_space_membership s P).mp hP with ⟨hpdeg, hp1, hp2⟩
  have hdeg (i : Fin 4) : Q.degreeOf i + 2 = P.degreeOf i := by
    rw [hQ, MvPolynomial.degreeOf_mul_eq hc hQ0, hcd, add_comm]
  have hfirst : swapFirstPair Q = Q := by
    apply mul_left_cancel₀ hc
    calc
      collisionFactor * swapFirstPair Q = swapFirstPair (collisionFactor * Q) := by
        rw [swapFirstPair_mul, hc1]
      _ = collisionFactor * Q := by rw [← hQ, hp1, hQ]
  have hsecond : swapSecondPair Q = Q := by
    apply mul_left_cancel₀ hc
    calc
      collisionFactor * swapSecondPair Q = swapSecondPair (collisionFactor * Q) := by
        rw [swapSecondPair_mul, hc2]
      _ = collisionFactor * Q := by rw [← hQ, hp2, hQ]
  refine ⟨Q, hQ0, hQ, (symmetric_space_membership s Q).mpr ⟨?_, hfirst, hsecond⟩,
    hdeg, ?_⟩
  · intro i
    have := hdeg i
    have := hpdeg i
    omega
  · have := hdeg 0
    omega

end Paper170

end
end

section

noncomputable section
open MvPolynomial
namespace Paper170

/-- The three extra factors in the local test have the degree vector printed in the paper. -/
theorem local_weight_degrees (i : Fin 4) :
    ((X 1 - X 3) * (X 1 - X 2) * (X 3 - X 0) : Poly4).degreeOf i =
      (![1, 2, 1, 2] : Fin 4 → ℕ) i := by
  have h13 := (difference_prime 1 3 (by decide)).ne_zero
  have h12 := (difference_prime 1 2 (by decide)).ne_zero
  have h30 := (difference_prime 3 0 (by decide)).ne_zero
  rw [degreeOf_mul_eq (mul_ne_zero h13 h12) h30, degreeOf_mul_eq h13 h12]
  fin_cases i <;> norm_num [difference_degree, Fin.ext_iff,
    show (1 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 2 by decide,
    show (3 : Fin 4) ≠ 0 by decide]

/-- Identifying any two variables leaves a polynomial ring in the other three. -/
theorem difference_quotient_polynomial (i j : Fin 4) (hij : i ≠ j) :
    Nonempty ((Poly4 ⧸ Ideal.span ({X i - X j} : Set Poly4)) ≃ₐ[ℝ]
      MvPolynomial (Fin 3) ℝ) := by
  classical
  let collapse : Fin 4 → {k : Fin 4 // k ≠ i} := fun k =>
    if h : k = i then ⟨j, hij.symm⟩ else ⟨k, h⟩
  let φ : Poly4 →ₐ[ℝ] MvPolynomial {k : Fin 4 // k ≠ i} ℝ := rename collapse
  let insert : MvPolynomial {k : Fin 4 // k ≠ i} ℝ →ₐ[ℝ] Poly4 := rename Subtype.val
  have hs : Function.Surjective φ := by
    apply rename_surjective
    intro k
    refine ⟨k.val, ?_⟩
    simp [collapse, k.property]
  have hk : RingHom.ker φ.toRingHom = Ideal.span ({X i - X j} : Set Poly4) := by
    ext P
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    change φ P = 0 ↔ (X i - X j : Poly4) ∣ P
    constructor
    · intro hp
      have hx : ∀k, (X i - X j : Poly4) ∣ X k - (insert.comp φ) (X k) := by
        intro k
        by_cases hki : k = i
        · subst k
          simp [insert, φ, collapse]
        · simp [insert, φ, collapse, hki]
      have h := substitution_difference_dvd (X i - X j) (insert.comp φ) hx P
      simpa [hp] using h
    · rintro ⟨Q, rfl⟩
      simp [φ, collapse, hij.symm]
  exact ⟨(Ideal.quotientEquivAlgOfEq ℝ hk.symm).trans
    ((Ideal.quotientKerAlgEquivOfSurjective hs).trans
      (renameEquiv ℝ (finSuccAboveEquiv (p := i)).symm))⟩

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

def diagonalUnivariate (u v : ℝ) : Poly4 →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C u, Polynomial.X, Polynomial.C v]

lemma diagonalUnivariate_monomial (u v : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    diagonalUnivariate u v (monomial m c) =
      Polynomial.C (c * u ^ m 1 * v ^ m 3) * Polynomial.X ^ (m 0 + m 2) := by
  simp only [diagonalUnivariate, MvPolynomial.aeval_monomial,
    Polynomial.algebraMap_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four, pow_add]
    ring
  · intro i
    simp

lemma diagonalUnivariate_bound (s : ℕ) (P : endpointSymmetricSpace s) (u v : ℝ) :
    (diagonalUnivariate u v P.val).natDegree ≤ 2 * (s - 2) := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).1
  rw [P.val.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [diagonalUnivariate_monomial]
  have h0 := degreeOf_le_iff.mp (hp 0) m hm
  have h2 := degreeOf_le_iff.mp (hp 2) m hm
  calc
    (Polynomial.C (P.val.coeff m * u ^ m 1 * v ^ m 3) *
      Polynomial.X ^ (m 0 + m 2)).natDegree ≤ m 0 + m 2 := by
        simpa using Polynomial.natDegree_C_mul_le (P.val.coeff m * u ^ m 1 * v ^ m 3)
          (Polynomial.X ^ (m 0 + m 2) : Polynomial ℝ)
    _ ≤ 2 * (s - 2) := by omega

lemma diagonalUnivariate_eval (u v x : ℝ) (P : Poly4) :
    (diagonalUnivariate u v P).eval x = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [diagonalUnivariate, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [map_mul, Polynomial.eval_mul]
    rw [hP]
    fin_cases i <;> simp [diagonalUnivariate, evalFour, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma diagonal_eval (P : Poly4) (x u v : ℝ) :
    MvPolynomial.eval ![x, u, v] (diagonalSpecialization P) = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [diagonalSpecialization, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [diagonalSpecialization, evalFour, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma vertex_eval (P : Poly4) (x u v : ℝ) :
    evalTwo u v (vertexSpecialization x P) = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [vertexSpecialization, evalFour, evalTwo]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    change MvPolynomial.aeval ![u, v] _ = MvPolynomial.aeval ![x, u, x, v] _
    change MvPolynomial.aeval ![u, v] _ = MvPolynomial.aeval ![x, u, x, v] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [vertexSpecialization, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma diagonal_zero_of_vertices (s : ℕ) (node : Fin (2 * s + 1) → ℝ)
    (hn : Function.Injective node) (P : endpointSymmetricSpace s)
    (hP : ∀ i, vertexSpecialization (node i) P.val = 0) :
    diagonalSpecialization P.val = 0 := by
  have hpoly (u v : ℝ) : diagonalUnivariate u v P.val = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hn
    · intro i
      rw [diagonalUnivariate_eval, ← vertex_eval, hP, map_zero]
    · have h := diagonalUnivariate_bound s P u v
      simp only [Fintype.card_fin]
      omega
  apply MvPolynomial.funext
  intro t
  have ht : t = ![t 0, t 1, t 2] := by ext i; fin_cases i <;> rfl
  rw [ht, diagonal_eval, ← diagonalUnivariate_eval, hpoly]
  simp

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem box_rename {d : ℕ} {P : Poly4} (hP : P ∈ box4 d) (e : Equiv.Perm (Fin 4)) :
    rename e P ∈ box4 d := by
  apply (box4_membership _ _).mpr
  intro i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [degreeOf_rename_of_injective e.injective]
  exact (box4_membership _ _).mp hP j

theorem coeff_rename_tuple {d : ℕ} (e : Equiv.Perm (Fin 4)) (P : Poly4)
    (t : BoundedExponents d) :
    (rename e P).coeff (tupleExponent t) =
      P.coeff (tupleExponent (fun i => t (e i))) := by
  have he : (tupleExponent (fun i => t (e i))).mapDomain e = tupleExponent t := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  rw [← he, coeff_rename_mapDomain e e.injective]

theorem box_coeff_ext {d : ℕ} {P Q : Poly4} (hP : P ∈ box4 d) (hQ : Q ∈ box4 d)
    (h : ∀ t : BoundedExponents d, P.coeff (tupleExponent t) = Q.coeff (tupleExponent t)) :
    P = Q := by
  have he : (⟨P, hP⟩ : box4 d) = ⟨Q, hQ⟩ := by
    apply (boxBasis d).repr.injective
    ext t
    exact h t
  exact congrArg Subtype.val he

theorem tuple4_eta {α : Type*} (t : Fin 4 → α) : ![t 0, t 1, t 2, t 3] = t := by
  funext i
  fin_cases i <;> simp

abbrev SymmetricCoordinate (d : ℕ) := Sym2 (Fin (d + 1)) × Sym2 (Fin (d + 1))

def tupleOrbit {d : ℕ} (t : BoundedExponents d) : SymmetricCoordinate d :=
  (s(t 0, t 1), s(t 2, t 3))

theorem tupleOrbit_swap_first {d : ℕ} (t : BoundedExponents d) :
    tupleOrbit (fun i => t (Equiv.swap (0 : Fin 4) 1 i)) = tupleOrbit t := by
  change (s(t 1, t 0), s(t 2, t 3)) = (s(t 0, t 1), s(t 2, t 3))
  exact Prod.ext Sym2.eq_swap rfl

theorem tupleOrbit_swap_second {d : ℕ} (t : BoundedExponents d) :
    tupleOrbit (fun i => t (Equiv.swap (2 : Fin 4) 3 i)) = tupleOrbit t := by
  change (s(t 0, t 1), s(t 3, t 2)) = (s(t 0, t 1), s(t 2, t 3))
  exact Prod.ext rfl Sym2.eq_swap

theorem symmetric_coeff_first {s : ℕ} (P : endpointSymmetricSpace s)
    (a b c d : Fin (s - 2 + 1)) :
    P.val.coeff (tupleExponent ![a, b, c, d]) = P.val.coeff (tupleExponent ![b, a, c, d]) := by
  have he : (fun i => (![a, b, c, d] : BoundedExponents (s - 2))
      (Equiv.swap (0 : Fin 4) 1 i)) = ![b, a, c, d] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.1
  change rename (Equiv.swap (0 : Fin 4) 1) P.val = P.val at hp
  have hc := coeff_rename_tuple (Equiv.swap (0 : Fin 4) 1) P.val ![a, b, c, d]
  rwa [he, hp] at hc

theorem symmetric_coeff_second {s : ℕ} (P : endpointSymmetricSpace s)
    (a b c d : Fin (s - 2 + 1)) :
    P.val.coeff (tupleExponent ![a, b, c, d]) = P.val.coeff (tupleExponent ![a, b, d, c]) := by
  have he : (fun i => (![a, b, c, d] : BoundedExponents (s - 2))
      (Equiv.swap (2 : Fin 4) 3 i)) = ![a, b, d, c] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.2
  change rename (Equiv.swap (2 : Fin 4) 3) P.val = P.val at hp
  have hc := coeff_rename_tuple (Equiv.swap (2 : Fin 4) 3) P.val ![a, b, c, d]
  rwa [he, hp] at hc

def symmetricCoefficients {s : ℕ} (P : endpointSymmetricSpace s) :
    SymmetricCoordinate (s - 2) → ℝ := fun q =>
  Sym2.lift₂ ⟨(fun a b c d => P.val.coeff (tupleExponent ![a, b, c, d])),
    fun a b c d => ⟨symmetric_coeff_first P a b c d, symmetric_coeff_second P a b c d⟩⟩ q.1 q.2

@[simp] theorem symmetricCoefficients_orbit {s : ℕ} (P : endpointSymmetricSpace s)
    (t : BoundedExponents (s - 2)) :
    symmetricCoefficients P (tupleOrbit t) = P.val.coeff (tupleExponent t) := by
  simp [symmetricCoefficients, tupleOrbit, tuple4_eta]

def realizeBox (d : ℕ) (f : SymmetricCoordinate d → ℝ) : box4 d :=
  (boxBasis d).equivFun.symm (fun t => f (tupleOrbit t))

@[simp] theorem realizeBox_coeff (d : ℕ) (f : SymmetricCoordinate d → ℝ)
    (t : BoundedExponents d) :
    (realizeBox d f).val.coeff (tupleExponent t) = f (tupleOrbit t) := by
  change (boxBasis d).equivFun ((boxBasis d).equivFun.symm _) t = _
  rw [LinearEquiv.apply_symm_apply]

theorem realizeBox_symmetric (s : ℕ) (f : SymmetricCoordinate (s - 2) → ℝ) :
    (realizeBox (s - 2) f).val ∈ endpointSymmetricSpace s := by
  apply (symmetric_space_membership _ _).mpr
  refine ⟨(box4_membership _ _).mp (realizeBox (s - 2) f).property, ?_, ?_⟩
  · apply box_coeff_ext (box_rename (realizeBox (s - 2) f).property _)
      (realizeBox (s - 2) f).property
    intro t
    change (rename (Equiv.swap (0 : Fin 4) 1) _).coeff (tupleExponent t) = _
    rw [coeff_rename_tuple, realizeBox_coeff, realizeBox_coeff, tupleOrbit_swap_first]
  · apply box_coeff_ext (box_rename (realizeBox (s - 2) f).property _)
      (realizeBox (s - 2) f).property
    intro t
    change (rename (Equiv.swap (2 : Fin 4) 3) _).coeff (tupleExponent t) = _
    rw [coeff_rename_tuple, realizeBox_coeff, realizeBox_coeff, tupleOrbit_swap_second]

def realizeSymmetric (s : ℕ) (f : SymmetricCoordinate (s - 2) → ℝ) : endpointSymmetricSpace s :=
  ⟨(realizeBox (s - 2) f).val, realizeBox_symmetric s f⟩

def symmetricCoordinatesEquiv (s : ℕ) :
    endpointSymmetricSpace s ≃ₗ[ℝ] (SymmetricCoordinate (s - 2) → ℝ) where
  toFun := symmetricCoefficients
  invFun := realizeSymmetric s
  left_inv P := by
    apply Subtype.ext
    apply box_coeff_ext (realizeBox (s - 2) (symmetricCoefficients P)).property
      ((box4_membership _ _).mpr ((symmetric_space_membership _ _).mp P.property).1)
    intro t
    rw [realizeBox_coeff, symmetricCoefficients_orbit]
  right_inv f := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients, realizeSymmetric, realizeBox_coeff, tupleOrbit]
  map_add' P Q := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients]
  map_smul' c P := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients]

theorem symmetric_space_dimension (s : ℕ) (hs : 2 ≤ s) :
    Module.finrank ℝ (endpointSymmetricSpace s) = (Nat.choose s 2) ^ 2 := by
  rw [(symmetricCoordinatesEquiv s).finrank_eq, Module.finrank_pi]
  simp only [SymmetricCoordinate, Fintype.card_prod, Sym2.card, Fintype.card_fin]
  have he : s - 2 + 1 + 1 = s := by omega
  rw [he]
  ring

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

lemma collisionFactors_prime (i : Fin 4) : Prime (collisionFactors i) := by
  fin_cases i <;> exact difference_prime _ _ (by decide)

lemma collisionFactors_coprime :
    Pairwise (fun i j : Fin 4 => IsRelPrime (collisionFactors i) (collisionFactors j)) := by
  intro i j hij
  rw [(collisionFactors_prime i).irreducible.isRelPrime_iff_not_dvd,
    (collisionFactors_prime i).dvd_prime_iff_associated (collisionFactors_prime j)]
  exact collision_factors_nonassociate hij

lemma collision_divides_of_diagonal_vanishing (s : ℕ) (P : endpointSymmetricSpace s)
    (hP : diagonalSpecialization P.val = 0) : collisionFactor ∣ P.val := by
  have h02 := (diagonal_vanishing_iff_divisible P.val).mp hP
  rcases (symmetric_space_membership s P.val).mp P.property with ⟨_, hp1, hp2⟩
  have h03 : (X 0 - X 3 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h02
    refine ⟨swapSecondPair Q, ?_⟩
    have h := congrArg swapSecondPair hQ
    rw [hp2, swapSecondPair_mul] at h
    simpa [swapSecondPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have h12 : (X 1 - X 2 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h02
    refine ⟨swapFirstPair Q, ?_⟩
    have h := congrArg swapFirstPair hQ
    rw [hp1, swapFirstPair_mul] at h
    simpa [swapFirstPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have h13 : (X 1 - X 3 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h03
    refine ⟨swapFirstPair Q, ?_⟩
    have h := congrArg swapFirstPair hQ
    rw [hp1, swapFirstPair_mul] at h
    simpa [swapFirstPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have hdvd (i : Fin 4) : collisionFactors i ∣ P.val := by
    fin_cases i
    · exact h02
    · exact h03
    · exact h12
    · exact h13
  have h := Finset.prod_dvd_of_isRelPrime
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) j _ hij =>
      collisionFactors_coprime hij) (fun i _ => hdvd i)
  simpa [Fin.prod_univ_four, collisionFactors, collisionFactor,
    Matrix.cons_val_two, Matrix.cons_val_three] using h

end Paper170

end
end

end OAI
