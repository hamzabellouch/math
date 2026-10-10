import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Restriction and obstruction along projective lines
-/

section

/-!
An alternative square-case obstruction on three components of a reduced line
arrangement. This is an exact polynomial gluing obstruction; it does not assume
or prove a deformation-to-normal-cone specialization theorem.
Coordinates on each line use U=-x, so the nodes of components 0,1,2 are U=1,2,3.
-/
namespace Nagata.W04.ReducibleSquare
open Polynomial

/-- The two positive integral cycle products have different positive powers. -/
theorem cycle_products_ne {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 0 < k) (ht : 0 < t) :
    (((k : K) + 2) * 3) ^ t ≠ (((k : K) + 3) * 2) ^ t := by
  have hlt : (2 * (k + 3)) ^ t < (3 * (k + 2)) ^ t :=
    Nat.pow_lt_pow_left (by omega) (Nat.ne_of_gt ht)
  intro heq
  have heq' : (3 * (k + 2)) ^ t = (2 * (k + 3)) ^ t := by
    exact_mod_cast (show ((3 : K) * ((k : K) + 2)) ^ t =
      ((2 : K) * ((k : K) + 3)) ^ t by simpa [mul_comm] using heq)
  omega

/-- Three node equations force every scalar on the triangle to vanish. -/
theorem cycle_coefficients_zero {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 0 < k) (ht : 0 < t) (c₀ c₁ c₂ : K)
    (h₀₁ : c₀ * ((k : K) + 2) ^ t = c₁ * 2 ^ t)
    (h₁₂ : c₁ = c₂)
    (h₂₀ : c₂ * 3 ^ t = c₀ * ((k : K) + 3) ^ t) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have hcycle : c₀ * (((k : K) + 2) * 3) ^ t =
      c₀ * (((k : K) + 3) * 2) ^ t := by
    calc
      _ = (c₀ * ((k : K) + 2) ^ t) * 3 ^ t := by rw [mul_pow]; ring
      _ = (c₁ * 2 ^ t) * 3 ^ t := by rw [h₀₁]
      _ = (c₂ * 3 ^ t) * 2 ^ t := by rw [h₁₂]; ring
      _ = (c₀ * ((k : K) + 3) ^ t) * 2 ^ t := by rw [h₂₀]
      _ = _ := by rw [mul_pow]; ring
  have hc₀ : c₀ = 0 := by
    by_contra hn
    exact cycle_products_ne k t hk ht (mul_left_cancel₀ hn hcycle)
  have hc₁ : c₁ = 0 := by
    have hn : (2 : K) ^ t ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hc₀, zero_mul] at h₀₁
    exact (mul_eq_zero.mp h₀₁.symm).resolve_right hn
  exact ⟨hc₀, hc₁, h₁₂ ▸ hc₁⟩

/-- Node gluing for the explicit common-tail polynomials forces the triangle to vanish. -/
theorem polynomial_triangle_zero {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 0 < k) (ht : 0 < t) (T : K[X])
    (hT₁ : T.eval 1 ≠ 0) (hT₂ : T.eval 2 ≠ 0) (hT₃ : T.eval 3 ≠ 0)
    (c₀ c₁ c₂ : K)
    (h₀₁ : (C c₀ * ((X + C ((k : K) + 1)) * T) ^ t).eval 1 =
      (C c₁ * ((X + C 1) * T) ^ t).eval 1)
    (h₁₂ : (C c₁ * ((X + C 1) * T) ^ t).eval 3 =
      (C c₂ * ((X + C 1) * T) ^ t).eval 3)
    (h₂₀ : (C c₂ * ((X + C 1) * T) ^ t).eval 2 =
      (C c₀ * ((X + C ((k : K) + 1)) * T) ^ t).eval 2) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X] at h₀₁ h₁₂ h₂₀
  have h₀₁' : c₀ * ((k : K) + 2) ^ t = c₁ * 2 ^ t := by
    apply mul_right_cancel₀ (pow_ne_zero t hT₁)
    simpa only [show (1 : K) + ((k : K) + 1) = (k : K) + 2 by ring,
      show (1 : K) + 1 = 2 by norm_num, mul_pow, mul_assoc] using h₀₁
  have h₁₂' : c₁ = c₂ := by
    apply mul_right_cancel₀ (pow_ne_zero t (mul_ne_zero (by norm_num : (3 : K) + 1 ≠ 0) hT₃))
    exact h₁₂
  have h₂₀' : c₂ * 3 ^ t = c₀ * ((k : K) + 3) ^ t := by
    apply mul_right_cancel₀ (pow_ne_zero t hT₂)
    simpa only [show (2 : K) + ((k : K) + 1) = (k : K) + 3 by ring,
      show (2 : K) + 1 = 3 by norm_num, mul_pow, mul_assoc] using h₂₀
  exact cycle_coefficients_zero k t hk ht c₀ c₁ c₂ h₀₁' h₁₂' h₂₀'

/-- Equality in the degree bound gives scalar-times-full-mark-product. -/
theorem polynomial_shape_of_mark_divisibility {K : Type*} [Field K]
    (f P : K[X]) (k t : ℕ) (hP : P.Monic) (hdegree : P.natDegree = k)
    (hfdegree : f.natDegree ≤ k * t) (hdiv : P ^ t ∣ f) :
    f = C f.leadingCoeff * P ^ t := by
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (hP.pow t) hdiv
  simpa [hP.natDegree_pow, hdegree, mul_comm] using hfdegree

end Nagata.W04.ReducibleSquare

end

section

/-! A prime of a one-variable polynomial ring disjoint from its nonzero
coefficients has height at most one, by localization to the fraction field. -/
noncomputable section
namespace Nagata.W04.Dimension
open Polynomial
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDomain R]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
theorem polynomial_height_le_one (I : Ideal R[X]) [I.IsPrime]
    (hC : I.comap Polynomial.C = ⊥) : I.height ≤ 1 := by
  let K := FractionRing R
  let M : Submonoid R[X] := (nonZeroDivisors R).map Polynomial.C
  have hd : Disjoint (M : Set R[X]) (I : Set R[X]) := by
    refine Set.disjoint_left.mpr ?_
    rintro p ⟨r, hr, rfl⟩ hp
    have hr0 : r = 0 := by
      have : r ∈ I.comap Polynomial.C := hp
      simpa [hC] using this
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hr0
  let J : Ideal K[X] := I.map (algebraMap R[X] K[X])
  have : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M K[X] I inferInstance hd
  have he : J.height = I.height := IsLocalization.height_map_of_disjoint M I hd
  rw [← he]
  apply (Ideal.height_le_iff (n := 1)).mpr
  intro Q hQ hQJ
  have : Q.IsPrime := hQ
  have hQ0 : Q = ⊥ := by
    by_contra hQ0
    have : Q.IsMaximal := IsPrime.to_maximal_ideal hQ0
    exact hQJ.ne (Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' hQJ.le)
  simp [hQ0]

theorem prime_height_eq_one_of_le_one (I : Ideal R) [I.IsPrime]
    (hI : I ≠ ⊥) (hle : I.height ≤ 1) : I.height = 1 := by
  apply le_antisymm hle
  have h := Ideal.height_add_one_le_of_lt_of_isPrime (I := (⊥ : Ideal R))
    (J := I) (bot_lt_iff_ne_bot.mpr hI)
  simpa only [Ideal.height_bot, zero_add] using h

end Nagata.W04.Dimension

end
end

section

noncomputable section
namespace Nagata.W04.Dimension
open MvPolynomial

variable (K : Type*) [Field K] (n : ℕ)

def lastVariableEquiv : MvPolynomial (Fin (n + 1)) K ≃ₐ[K]
    Polynomial (MvPolynomial (Fin n) K) :=
  (MvPolynomial.renameEquiv K finSuccEquivLast).trans
    (MvPolynomial.optionEquivLeft K (Fin n))

theorem lastVariableEquiv_symm_C (p : MvPolynomial (Fin n) K) :
    (lastVariableEquiv K n).symm (Polynomial.C p) =
      MvPolynomial.rename Fin.castSucc p := by
  have h : (lastVariableEquiv K n).symm.toAlgHom.comp Polynomial.CAlgHom =
      MvPolynomial.rename (R := K) Fin.castSucc := by
    ext i
    simp [lastVariableEquiv, MvPolynomial.optionEquivLeft_symm_C_X]
  exact DFunLike.congr_fun h p

variable {K n}

theorem height_le_one_of_independent_quotient
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hind : AlgebraicIndependent K
      (fun i : Fin n => Ideal.Quotient.mk I (MvPolynomial.X i.castSucc))) :
    I.height ≤ 1 := by
  let e := lastVariableEquiv K n
  let J := I.comap e.symm.toRingEquiv.toRingHom
  have : J.IsPrime := Ideal.comap_isPrime _ I
  have hmap : (Ideal.Quotient.mkₐ K I).comp
      (MvPolynomial.rename Fin.castSucc) =
      MvPolynomial.aeval (fun i : Fin n => Ideal.Quotient.mk I
        (MvPolynomial.X i.castSucc)) := by
    ext i
    simp
  have hC : J.comap Polynomial.C = ⊥ := by
    apply bot_unique
    intro p hp
    have hzero : Ideal.Quotient.mk I (MvPolynomial.rename Fin.castSucc p) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change e.symm (Polynomial.C p) ∈ I at hp
      simpa [e, lastVariableEquiv_symm_C] using hp
    have hp0 : p = 0 := hind (by
      rw [← hmap]
      simpa using hzero)
    simpa using hp0
  have hheight : J.height = I.height := e.symm.toRingEquiv.height_comap I
  rw [← hheight]
  exact polynomial_height_le_one J hC

theorem height_eq_one_of_independent_quotient
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hI : I ≠ ⊥)
    (hind : AlgebraicIndependent K
      (fun i : Fin n => Ideal.Quotient.mk I (MvPolynomial.X i.castSucc))) :
    I.height = 1 :=
  prime_height_eq_one_of_le_one I hI (height_le_one_of_independent_quotient I hind)

end Nagata.W04.Dimension

end
end

section

/-! Actual restrictions of plane forms to the tangent-parabola line arrangement. -/
noncomputable section
namespace Nagata.W04.ReducibleSquare

variable {K : Type*} [Field K]

/-- Homogeneous coordinates on Y=i²-iU in the affine parameter U. -/
def lineSubstitution (i : K) : Fin 3 → Polynomial K :=
  ![Polynomial.X, Polynomial.C (i ^ 2) - Polynomial.C i * Polynomial.X, 1]

/-- The actual polynomial restriction homomorphism from plane forms to component i. -/
def lineRestriction (i : K) : MvPolynomial (Fin 3) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (lineSubstitution i)

/-- Actual ambient forms automatically glue at each pairwise node. -/
theorem lineRestriction_node_gluing (F : MvPolynomial (Fin 3) K) (i j : K) :
    (lineRestriction i F).eval (i + j) = (lineRestriction j F).eval (i + j) := by
  change Polynomial.evalRingHom (i + j) (MvPolynomial.eval₂Hom _ _ F) =
    Polynomial.evalRingHom (i + j) (MvPolynomial.eval₂Hom _ _ F)
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.map_eval₂Hom]
  have hcoords : (fun v => Polynomial.evalRingHom (i + j) (lineSubstitution i v)) =
      (fun v => Polynomial.evalRingHom (i + j) (lineSubstitution j v)) := by
    funext v
    fin_cases v <;> simp [lineSubstitution]
    ring
  rw [hcoords]

/-- The affine equation of component i. -/
def lineEquation (i x y : K) : K := y + i * x - i ^ 2

/-- Restricting another line equation to component i gives the node factor. -/
theorem lineEquation_on_component (i j x : K) :
    lineEquation j x (i ^ 2 - i * x) = (j - i) * (x - i - j) := by
  unfold lineEquation
  ring

/-- Negative integer marked coordinates avoid every other component. -/
theorem marked_point_avoids_other_line [CharZero K] (i j v : ℕ)
    (hij : i ≠ j) (hv : 0 < v) :
    lineEquation (j : K) (-(v : K)) ((i : K) ^ 2 - (i : K) * (-(v : K))) ≠ 0 := by
  rw [lineEquation_on_component]
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hij)
  · have hsum : ((v + i + j : ℕ) : K) ≠ 0 := by exact_mod_cast (show v + i + j ≠ 0 by omega)
    convert neg_ne_zero.mpr hsum using 1
    push_cast
    ring

end Nagata.W04.ReducibleSquare

end
end

section

/-! Explicit rational marks for the reducible square-case construction. -/
noncomputable section
namespace Nagata.W04.ReducibleSquare
open Polynomial

/-- The common marks with affine x-coordinates 2,...,k, in the parameter U=-x. -/
def markTail {K : Type*} [CommSemiring K] (k : ℕ) : K[X] :=
  ∏ j ∈ Finset.range (k - 1), (X + C ((j + 2 : ℕ) : K))

/-- First marked x-coordinate: k+1 on component zero and 1 on all others. -/
def firstMark (k i : ℕ) : ℕ := if i = 0 then k + 1 else 1

/-- Actual polynomial vanishing at the k chosen marks on component i. -/
def markPolynomial {K : Type*} [CommSemiring K] (k i : ℕ) : K[X] :=
  (X + C ((firstMark k i : ℕ) : K)) * markTail k

variable {K : Type*} [Field K]

 theorem markTail_monic (k : ℕ) : (markTail k : K[X]).Monic := by
  exact monic_prod_of_monic _ _ (fun j _ => monic_X_add_C _)

 theorem markTail_natDegree (k : ℕ) : (markTail k : K[X]).natDegree = k - 1 := by
  unfold markTail
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C _)]
  simp_rw [natDegree_X_add_C]
  simp

 theorem markPolynomial_monic (k i : ℕ) : (markPolynomial k i : K[X]).Monic :=
  (monic_X_add_C _).mul (markTail_monic k)

 theorem markPolynomial_natDegree (k i : ℕ) (hk : 0 < k) :
    (markPolynomial k i : K[X]).natDegree = k := by
  unfold markPolynomial
  rw [(monic_X_add_C _).natDegree_mul (markTail_monic k), natDegree_X_add_C,
    markTail_natDegree]
  omega

variable [CharZero K]

 theorem markTail_eval_nat_ne_zero (k n : ℕ) : (markTail k : K[X]).eval (n : K) ≠ 0 := by
  unfold markTail
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_add, eval_X, eval_C]
  exact_mod_cast (show n + (j + 2) ≠ 0 by omega)

 theorem firstMark_pos (k i : ℕ) : 0 < firstMark k i := by
  unfold firstMark
  split <;> omega

 theorem markPolynomial_eval_nat_ne_zero (k i n : ℕ) :
    (markPolynomial k i : K[X]).eval (n : K) ≠ 0 := by
  unfold markPolynomial
  rw [eval_mul, eval_add, eval_X, eval_C]
  apply mul_ne_zero _ (markTail_eval_nat_ne_zero k n)
  exact_mod_cast (show n + firstMark k i ≠ 0 by have := firstMark_pos k i; omega)

 theorem marked_linear_factors_coprime (u v : ℕ) (huv : u ≠ v) :
    IsCoprime (X + C (u : K)) (X + C (v : K)) := by
  have huv' : -(u : K) ≠ -(v : K) := by
    intro h
    have h' : (u : K) = (v : K) := neg_injective h
    exact huv (Nat.cast_injective h')
  simpa only [C_neg, sub_neg_eq_add] using
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr huv').isUnit)

 theorem firstMark_ne_tail (k i j : ℕ) (hj : j < k - 1) : firstMark k i ≠ j + 2 := by
  unfold firstMark
  split <;> omega

/-- Ordinary marked-point factor divisibility gives the full k-mark product power. -/
theorem markPolynomial_pow_dvd (k i t : ℕ) (f : K[X])
    (hfirst : (X + C ((firstMark k i : ℕ) : K)) ^ t ∣ f)
    (htail : ∀ j < k - 1, (X + C ((j + 2 : ℕ) : K)) ^ t ∣ f) :
    (markPolynomial k i : K[X]) ^ t ∣ f := by
  have htaildiv : (markTail k : K[X]) ^ t ∣ f := by
    unfold markTail
    rw [← Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · intro u hu v hv huv
      exact (marked_linear_factors_coprime (u + 2) (v + 2) (by omega)).pow
    · intro j hj
      exact htail j (Finset.mem_range.mp hj)
  have hcop : IsCoprime (X + C ((firstMark k i : ℕ) : K)) (markTail k : K[X]) := by
    apply IsCoprime.prod_right
    intro j hj
    exact marked_linear_factors_coprime _ _ (firstMark_ne_tail k i j (Finset.mem_range.mp hj))
  unfold markPolynomial
  rw [mul_pow]
  exact hcop.pow.mul_dvd hfirst htaildiv

/-- Equality-degree restrictions have the exact shape required by node gluing. -/
theorem marked_restriction_shape (k i t : ℕ) (hk : 0 < k) (f : K[X])
    (hdeg : f.natDegree ≤ k * t)
    (hfirst : (X + C ((firstMark k i : ℕ) : K)) ^ t ∣ f)
    (htail : ∀ j < k - 1, (X + C ((j + 2 : ℕ) : K)) ^ t ∣ f) :
    f = C f.leadingCoeff * (markPolynomial k i : K[X]) ^ t := by
  exact polynomial_shape_of_mark_divisibility f (markPolynomial k i) k t
    (markPolynomial_monic k i) (markPolynomial_natDegree k i hk) hdeg
    (markPolynomial_pow_dvd k i t f hfirst htail)

end Nagata.W04.ReducibleSquare

end
end

section

/-! The complete polynomial restriction obstruction for the squarefree k-line arrangement. -/
namespace Nagata.W04.ReducibleSquare
open Polynomial

/-- No nonzero family of equality-degree marked restrictions can glue at all nodes. -/
theorem line_family_zero {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 3 ≤ k) (ht : 0 < t) (f : ℕ → K[X])
    (hdeg : ∀ i < k, (f i).natDegree ≤ k * t)
    (hdiv : ∀ i < k, (markPolynomial k i : K[X]) ^ t ∣ f i)
    (hglue : ∀ i < k, ∀ j < k, (f i).eval ((i + j : ℕ) : K) =
      (f j).eval ((i + j : ℕ) : K)) :
    ∀ i < k, f i = 0 := by
  have hk₀ : 0 < k := by omega
  have hk₁ : 1 < k := by omega
  have hk₂ : 2 < k := by omega
  have hshape (i : ℕ) (hi : i < k) :
      f i = C (f i).leadingCoeff * (markPolynomial k i : K[X]) ^ t :=
    polynomial_shape_of_mark_divisibility (f i) (markPolynomial k i) k t
      (markPolynomial_monic k i) (markPolynomial_natDegree k i hk₀) (hdeg i hi) (hdiv i hi)
  have h₀₁ := hglue 0 hk₀ 1 hk₁
  have h₁₂ := hglue 1 hk₁ 2 hk₂
  have h₂₀ := hglue 2 hk₂ 0 hk₀
  rw [hshape 0 hk₀, hshape 1 hk₁] at h₀₁
  rw [hshape 1 hk₁, hshape 2 hk₂] at h₁₂
  rw [hshape 2 hk₂, hshape 0 hk₀] at h₂₀
  have hz := polynomial_triangle_zero k t hk₀ ht (markTail k : K[X])
    (by simpa using markTail_eval_nat_ne_zero (K := K) k 1)
    (by simpa using markTail_eval_nat_ne_zero (K := K) k 2)
    (by simpa using markTail_eval_nat_ne_zero (K := K) k 3)
    (f 0).leadingCoeff (f 1).leadingCoeff (f 2).leadingCoeff
    (by simpa [markPolynomial, firstMark] using h₀₁)
    (by simpa [markPolynomial, firstMark] using h₁₂)
    (by simpa [markPolynomial, firstMark] using h₂₀)
  have hf₀ : f 0 = 0 := by rw [hshape 0 hk₀, hz.1]; simp
  intro i hi
  have hnode := hglue i hi 0 hk₀
  rw [hf₀, eval_zero, hshape i hi, eval_mul, eval_C, eval_pow] at hnode
  have hc : (f i).leadingCoeff = 0 :=
    (mul_eq_zero.mp hnode).resolve_right
      (pow_ne_zero t (markPolynomial_eval_nat_ne_zero k i (i + 0)))
  rw [hshape i hi, hc]
  simp

/-- The same obstruction directly from multiplicity-factor conditions at each mark. -/
theorem line_family_zero_of_marked_factors {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 3 ≤ k) (ht : 0 < t) (f : ℕ → K[X])
    (hdeg : ∀ i < k, (f i).natDegree ≤ k * t)
    (hfirst : ∀ i < k, (X + C ((firstMark k i : ℕ) : K)) ^ t ∣ f i)
    (htail : ∀ i < k, ∀ j < k - 1, (X + C ((j + 2 : ℕ) : K)) ^ t ∣ f i)
    (hglue : ∀ i < k, ∀ j < k, (f i).eval ((i + j : ℕ) : K) =
      (f j).eval ((i + j : ℕ) : K)) :
    ∀ i < k, f i = 0 := by
  apply line_family_zero k t hk ht f hdeg
  · intro i hi
    exact markPolynomial_pow_dvd k i t (f i) (hfirst i hi) (htail i hi)
  · exact hglue

end Nagata.W04.ReducibleSquare

end

section

/-! The cycle obstruction for restrictions of an actual homogeneous-coordinate polynomial.
Degree and marked factor divisibility remain explicit inputs; node compatibility
is proved for the actual restriction map rather than assumed. -/
namespace Nagata.W04.ReducibleSquare
open Polynomial

/-- Every component restriction vanishes, with gluing discharged for ambient forms. -/
theorem ambient_restrictions_zero {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 3 ≤ k) (ht : 0 < t) (F : MvPolynomial (Fin 3) K)
    (hdeg : ∀ i < k, (lineRestriction (i : K) F).natDegree ≤ k * t)
    (hfirst : ∀ i < k, (X + C ((firstMark k i : ℕ) : K)) ^ t ∣ lineRestriction (i : K) F)
    (htail : ∀ i < k, ∀ j < k - 1,
      (X + C ((j + 2 : ℕ) : K)) ^ t ∣ lineRestriction (i : K) F) :
    ∀ i < k, lineRestriction (i : K) F = 0 := by
  apply line_family_zero_of_marked_factors k t hk ht (fun i => lineRestriction (i : K) F)
    hdeg hfirst htail
  intro i hi j hj
  simpa only [Nat.cast_add] using lineRestriction_node_gluing F (i : K) (j : K)

/-- An actual nonzero component restriction contradicts all the marked degree bounds. -/
theorem ambient_nonzero_restriction_obstruction {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 3 ≤ k) (ht : 0 < t) (F : MvPolynomial (Fin 3) K)
    (hdeg : ∀ i < k, (lineRestriction (i : K) F).natDegree ≤ k * t)
    (hfirst : ∀ i < k, (X + C ((firstMark k i : ℕ) : K)) ^ t ∣ lineRestriction (i : K) F)
    (htail : ∀ i < k, ∀ j < k - 1,
      (X + C ((j + 2 : ℕ) : K)) ^ t ∣ lineRestriction (i : K) F)
    (hNonzero : ∃ i < k, lineRestriction (i : K) F ≠ 0) : False := by
  obtain ⟨i, hi, hne⟩ := hNonzero
  exact hne (ambient_restrictions_zero k t hk ht F hdeg hfirst htail i hi)

end Nagata.W04.ReducibleSquare

end

end OAI
