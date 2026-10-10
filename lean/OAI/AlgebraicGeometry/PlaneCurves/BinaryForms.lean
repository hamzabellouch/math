import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Prime
import OAI.AlgebraicGeometry.PlaneCurves.Forms
import OAI.AlgebraicGeometry.PlaneCurves.LineObstructions

namespace OAI

/-!
# Binary homogeneous factorization and prime line equations
-/

section

/-! Degree control for genuine affine-linear substitution into a multivariate
polynomial. This closes the numerical degree premise in line restriction. -/
noncomputable section
namespace Nagata.W02

/-- Substituting polynomials of degree at most one cannot increase total degree. -/
theorem natDegree_eval₂_le_totalDegree {σ K : Type*} [CommSemiring K]
    (P : MvPolynomial σ K) (f : σ → Polynomial K)
    (hf : ∀ i, (f i).natDegree ≤ 1) :
    (P.eval₂ Polynomial.C f).natDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  calc
    (Polynomial.C (P.coeff d) * ∏ i ∈ d.support, f i ^ d i).natDegree ≤
        (Polynomial.C (P.coeff d)).natDegree +
          (∏ i ∈ d.support, f i ^ d i).natDegree := Polynomial.natDegree_mul_le
    _ = (∏ i ∈ d.support, f i ^ d i).natDegree := by simp
    _ ≤ ∑ i ∈ d.support, (f i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using Polynomial.natDegree_pow_le_of_le (d i) (hf i)
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

end Nagata.W02

end
end

section

/-! Shared genuine homogeneous-coefficient model for finite matrix and dimension
arguments. No geometric or cardinality conclusion is part of the definitions. -/
noncomputable section
namespace Nagata.W02

/-- Ternary exponent vectors with sum k. -/
def DegreeExponent (k : ℕ) := {d : Fin 3 →₀ ℕ // d.degree = k}

instance degreeExponentFintype (k : ℕ) : Fintype (DegreeExponent k) :=
  ((Finsupp.finite_of_degree_le (σ := Fin 3) k).subset
    (fun _ h => le_of_eq h)).fintype

/-- Proved identification with the actual supported coefficient submodule. -/
def homogeneousCoefficientEquiv (R : Type*) [CommRing R] (k : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) R k ≃ₗ[R] (DegreeExponent k →₀ R) :=
  (LinearEquiv.ofEq _ _
    (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 3) R k)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp {d : Fin 3 →₀ ℕ | d.degree = k})

@[simp] theorem homogeneousCoefficientEquiv_apply (R : Type*) [CommRing R]
    (k : ℕ) (F : MvPolynomial.homogeneousSubmodule (Fin 3) R k) (e : DegreeExponent k) :
    homogeneousCoefficientEquiv R k F e = F.val.coeff e.val := rfl

@[simp] theorem homogeneousCoefficientEquiv_symm_single (R : Type*) [CommRing R]
    (k : ℕ) (e : DegreeExponent k) (c : R) :
    (((homogeneousCoefficientEquiv R k).symm (Finsupp.single e c)) :
      MvPolynomial (Fin 3) R) = MvPolynomial.monomial e.val c := by
  apply AddMonoidAlgebra.coeff_injective
  change (((Finsupp.supportedEquivFinsupp (R := R)
    {d : Fin 3 →₀ ℕ | d.degree = k}).symm (Finsupp.single e c)) :
      (Fin 3 →₀ ℕ) →₀ R) = Finsupp.single e.val c
  exact Finsupp.supportedEquivFinsupp_symm_single _ e c

end Nagata.W02

end
end

section

/-! The exact dimension of degree-k ternary homogeneous forms, for the square
case's evaluation-map dimension argument. All objects are the actual mathlib
MvPolynomial homogeneous submodules. -/
noncomputable section
namespace Nagata.W02

/-- Explicit finite enumeration by the genuine finsupp antidiagonal. -/
def degreeExponentEquiv (k : ℕ) :
    DegreeExponent k ≃ ↥(Finset.finsuppAntidiag (Finset.univ : Finset (Fin 3)) k) where
  toFun d := ⟨d.val, by
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by simpa only [← Finsupp.degree_eq_sum] using d.property,
      Finset.subset_univ _⟩⟩
  invFun d := ⟨d.val, by
    have hd := (Finset.mem_finsuppAntidiag.mp d.property).1
    simpa only [← Finsupp.degree_eq_sum] using hd⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Stars and bars for three variables, with the exact binomial convention
required by the manuscript. -/
theorem card_degreeExponent (k : ℕ) :
    Fintype.card (DegreeExponent k) = (k + 2).choose 2 := by
  rw [Fintype.card_congr (degreeExponentEquiv k), Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  have he : 3 + k - 1 = k + 2 := by omega
  rw [he]
  exact Nat.choose_symm_add

/-- The monomial basis transported through the proved coefficient equivalence. -/
def homogeneousBasis (K : Type*) [Field K] (k : ℕ) :
    Module.Basis (DegreeExponent k) K (MvPolynomial.homogeneousSubmodule (Fin 3) K k) :=
  Finsupp.basisSingleOne.map (homogeneousCoefficientEquiv K k).symm

/-- Every basis vector is the genuine monomial with its advertised exponent. -/
theorem homogeneousBasis_coe (K : Type*) [Field K] (k : ℕ) (e : DegreeExponent k) :
    ((homogeneousBasis K k e) : MvPolynomial (Fin 3) K) = MvPolynomial.monomial e.val 1 := by
  simp [homogeneousBasis]

instance homogeneousFiniteDimensional (K : Type*) [Field K] (k : ℕ) :
    FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 3) K k) :=
  (homogeneousCoefficientEquiv K k).symm.finiteDimensional

/-- Exact dimension of genuine ternary homogeneous forms. -/
theorem finrank_homogeneousSubmodule (K : Type*) [Field K] (k : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 3) K k) =
      (k + 2).choose 2 := by
  rw [(homogeneousCoefficientEquiv K k).finrank_eq,
    Module.finrank_finsupp_self, card_degreeExponent]

end Nagata.W02

end
end

section

noncomputable section
namespace Nagata.W02
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Decoding a homogeneous coefficient vector and evaluating is exactly its
linear combination of evaluated monomials. -/
theorem aeval_homogeneousCoefficientEquiv_symm (d : ℕ) (s : Fin 3 → A)
    (c : DegreeExponent d →₀ K) :
    MvPolynomial.aeval s
      (((homogeneousCoefficientEquiv K d).symm c) : MvPolynomial (Fin 3) K) =
    Finsupp.linearCombination K
      (fun e : DegreeExponent d => MvPolynomial.aeval s (MvPolynomial.monomial e.val (1 : K))) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' => simp only [map_add, Submodule.coe_add, hc, hc']
  | single e a =>
    rw [homogeneousCoefficientEquiv_symm_single, Finsupp.linearCombination_single]
    simp [MvPolynomial.aeval_monomial, Algebra.smul_def]

end Nagata.W02

end
end

section

/-! Actual splitting of binary homogeneous complex polynomials. The coordinate
factor at infinity is retained with exponent d−natDegree(dehomogenization). -/
noncomputable section
namespace Nagata.W02
open MvPolynomial

abbrev BinaryForm := MvPolynomial (Fin 2) ℂ

def binaryLinear (r : ℂ) : BinaryForm := X 0 - C r * X 1

def binaryRootProduct (s : Multiset ℂ) : BinaryForm := (s.map binaryLinear).prod

def binaryAffineHom : BinaryForm →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then Polynomial.X else 1)

theorem binaryAffineHom_apply (F : BinaryForm) :
    binaryAffineHom F = Nagata.W16.binaryAffine F := rfl

theorem binaryLinear_homogeneous (r : ℂ) : (binaryLinear r).IsHomogeneous 1 := by
  exact (isHomogeneous_X ℂ (0 : Fin 2)).sub ((isHomogeneous_X ℂ (1 : Fin 2)).C_mul r)

theorem binaryLinear_ne_zero (r : ℂ) : binaryLinear r ≠ 0 := by
  intro hz
  have h := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)) hz
  simp [binaryLinear] at h

theorem binaryRootProduct_homogeneous (s : Multiset ℂ) :
    (binaryRootProduct s).IsHomogeneous s.card := by
  induction s using Multiset.induction_on with
  | empty => simpa [binaryRootProduct] using (isHomogeneous_one (Fin 2) ℂ)
  | @cons r s ih =>
    simpa [binaryRootProduct, Nat.add_comm] using (binaryLinear_homogeneous r).mul ih

@[simp] theorem binaryAffineHom_linear (r : ℂ) :
    binaryAffineHom (binaryLinear r) = Polynomial.X - Polynomial.C r := by
  rw [binaryLinear, map_sub, map_mul]
  simp [binaryAffineHom]

@[simp] theorem binaryAffineHom_rootProduct (s : Multiset ℂ) :
    binaryAffineHom (binaryRootProduct s) = (s.map (fun r => Polynomial.X - Polynomial.C r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [binaryRootProduct]
  | @cons r s ih =>
    simp only [binaryRootProduct, Multiset.map_cons, Multiset.prod_cons] at *
    rw [map_mul, binaryAffineHom_linear, ih]

/-- Exact projective factorization, including constant forms and all roots at
infinity. Every displayed factor is a nonzero homogeneous linear form. -/
theorem binary_homogeneous_factorization {F : BinaryForm} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) :
    ∃ (c : ℂ) (e : ℕ) (s : Multiset ℂ), c ≠ 0 ∧ e + s.card = d ∧
      F = C c * ((X 1 : BinaryForm) ^ e * binaryRootProduct s) := by
  let q := Nagata.W16.binaryAffine F
  have hq : q ≠ 0 := Nagata.W16.binaryAffine_ne_zero hF hF0
  have hqd : q.natDegree ≤ d := Nagata.W16.binaryAffine_natDegree_le hF
  have hroots : q.roots.card = q.natDegree := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  let G : BinaryForm := C q.leadingCoeff * (X 1 ^ (d - q.natDegree) * binaryRootProduct q.roots)
  have hG : G.IsHomogeneous d := by
    have hp := ((isHomogeneous_X ℂ (1 : Fin 2)).pow (d - q.natDegree)).mul
      (binaryRootProduct_homogeneous q.roots)
    have hh := hp.C_mul q.leadingCoeff
    simpa only [one_mul, hroots, Nat.sub_add_cancel hqd] using hh
  have heval : binaryAffineHom G = q := by
    change binaryAffineHom (C q.leadingCoeff * (X 1 ^ (d - q.natDegree) * binaryRootProduct q.roots)) = q
    rw [map_mul, map_mul, map_pow, binaryAffineHom_rootProduct]
    have hC : binaryAffineHom (C q.leadingCoeff) = Polynomial.C q.leadingCoeff := by
      simp [binaryAffineHom]
    have hX : binaryAffineHom (X 1) = (1 : Polynomial ℂ) := by simp [binaryAffineHom]
    rw [hC, hX, one_pow, one_mul]
    exact (IsAlgClosed.splits q).eq_prod_roots.symm
  have hzero : Nagata.W16.binaryAffine (F - G) = 0 := by
    change binaryAffineHom (F - G) = 0
    rw [map_sub, heval]
    change q - q = 0
    exact sub_self q
  have heq : F = G := sub_eq_zero.mp (Nagata.W16.binaryAffine_eq_zero_imp (hF.sub hG) hzero)
  exact ⟨q.leadingCoeff, d - q.natDegree, q.roots, Polynomial.leadingCoeff_ne_zero.mpr hq,
    by omega, heq⟩

end Nagata.W02

end
end

section

noncomputable section
namespace Nagata.W02

open Nagata.W04.ReducibleSquare

/-- The source's explicit line parameterization uses only affine-linear coordinates. -/
theorem lineSubstitution_natDegree_le {K : Type*} [Field K] (i : K) (j : Fin 3) :
    (lineSubstitution i j).natDegree ≤ 1 := by
  fin_cases j
  · simp [lineSubstitution]
  · change (Polynomial.C (i ^ 2) - Polynomial.C i * Polynomial.X).natDegree ≤ 1
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  · simp [lineSubstitution]

/-- Actual component restriction degree is bounded by ambient total degree. -/
theorem lineRestriction_natDegree_le_totalDegree {K : Type*} [Field K]
    (i : K) (P : MvPolynomial (Fin 3) K) :
    (lineRestriction i P).natDegree ≤ P.totalDegree :=
  natDegree_eval₂_le_totalDegree P (lineSubstitution i) (lineSubstitution_natDegree_le i)

end Nagata.W02

end
end

section

noncomputable section
namespace Nagata.W02
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous binary relation in a prime ideal forces a linear relation. -/
theorem binary_homogeneous_notMem {J : Ideal BinaryForm} (hJ : J.IsPrime)
    (hlin : ∀ a b : ℂ, C a * X 0 + C b * X 1 ∈ J → a = 0 ∧ b = 0)
    {F : BinaryForm} {d : ℕ} (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) : F ∉ J := by
  let := hJ
  have hX : (X 1 : BinaryForm) ∉ J := by
    intro h
    have := (hlin 0 1 (by simpa using h)).2
    exact one_ne_zero this
  have hL (r : ℂ) : binaryLinear r ∉ J := by
    intro h
    have := (hlin 1 (-r) (by simpa [binaryLinear, sub_eq_add_neg] using h)).1
    exact one_ne_zero this
  have hpow (e : ℕ) : (X 1 : BinaryForm) ^ e ∉ J := by
    induction e with
    | zero => simpa using hJ.one_notMem
    | succ e ih => simpa only [pow_succ, hJ.mul_mem_iff_mem_or_mem, not_or] using And.intro ih hX
  have hprod (s : Multiset ℂ) : binaryRootProduct s ∉ J := by
    induction s using Multiset.induction_on with
    | empty => simpa [binaryRootProduct] using hJ.one_notMem
    | @cons r s ih =>
      simpa only [binaryRootProduct, Multiset.map_cons, Multiset.prod_cons,
        hJ.mul_mem_iff_mem_or_mem, not_or] using And.intro (hL r) ih
  obtain ⟨c, e, s, hc, _, heq⟩ := binary_homogeneous_factorization hF hF0
  rw [heq, hJ.mul_mem_iff_mem_or_mem, not_or]
  refine ⟨Ideal.notMem_of_isUnit J ((isUnit_iff_ne_zero.mpr hc).map C), ?_⟩
  rw [hJ.mul_mem_iff_mem_or_mem, not_or]
  exact ⟨hpow e, hprod s⟩

/-- Component closure upgrades the homogeneous conclusion to every binary polynomial. -/
theorem binary_eq_zero_of_mem {J : Ideal BinaryForm} (hJ : J.IsPrime)
    (hcomp : ∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J)
    (hlin : ∀ a b : ℂ, C a * X 0 + C b * X 1 ∈ J → a = 0 ∧ b = 0)
    {F : BinaryForm} (hF : F ∈ J) : F = 0 := by
  have hz (d : ℕ) : homogeneousComponent d F = 0 := by
    by_contra hn
    exact binary_homogeneous_notMem hJ hlin (homogeneousComponent_isHomogeneous d F) hn
      (hcomp F hF d)
  rw [← sum_homogeneousComponent F]
  simp only [hz, Finset.sum_const_zero]

/-- Renaming preserves each ordinary homogeneous component, including collisions. -/
theorem homogeneousComponent_rename {σ ι : Type*} (e : σ → ι)
    (F : MvPolynomial σ ℂ) (d : ℕ) :
    homogeneousComponent d (rename e F) = rename e (homogeneousComponent d F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h := isHomogeneous_monomial a (show u.degree = u.degree from rfl)
    rw [homogeneousComponent_of_mem (h.rename_isHomogeneous (f := e)), homogeneousComponent_of_mem h]
    split_ifs <;> simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]

/-- Concrete ordinary component closure extracted from mathlib's graded ideal. -/
theorem component_mem_of_isHomogeneous {σ : Type*} {I : Ideal (MvPolynomial σ ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) {P : MvPolynomial σ ℂ}
    (hP : P ∈ I) (n : ℕ) : homogeneousComponent n P ∈ I := by
  have hh := hI n hP
  have hcomp (D : DirectSum.Decomposition (homogeneousSubmodule σ ℂ)) :
      (D.decompose' P n : MvPolynomial σ ℂ) = homogeneousComponent n P := by
    rw [Subsingleton.elim D MvPolynomial.decomposition,
      MvPolynomial.decomposition.decompose'_apply]
  rwa [← DirectSum.Decomposition.decompose'_eq, hcomp] at hh

/-- Two variables in a homogeneous prime quotient have no polynomial relation
if they have no linear relation. This statement uses genuine renamed polynomials. -/
theorem binary_rename_eq_zero_of_mem {σ : Type*} (e : Fin 2 → σ)
    {I : Ideal (MvPolynomial σ ℂ)} (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hlin : ∀ a b : ℂ, C a * X (e 0) + C b * X (e 1) ∈ I → a = 0 ∧ b = 0)
    {F : BinaryForm} (hF : rename e F ∈ I) : F = 0 := by
  let J : Ideal BinaryForm := Ideal.comap (rename e).toRingHom I
  have hJ : J.IsPrime := hI.comap _
  apply binary_eq_zero_of_mem hJ (J := J) ?_ ?_ hF
  · intro P hP d
    change rename e (homogeneousComponent d P) ∈ I
    rw [← homogeneousComponent_rename]
    exact component_mem_of_isHomogeneous hhom hP d
  · intro a b hab
    exact hlin a b (by simpa [J, Ideal.mem_comap] using hab)

/-- Algebraic independence of the two actual coordinate classes in the quotient. -/
theorem algebraicIndependent_quotient_of_no_linear_relation {σ : Type*}
    (e : Fin 2 → σ) {I : Ideal (MvPolynomial σ ℂ)} (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hlin : ∀ a b : ℂ, C a * X (e 0) + C b * X (e 1) ∈ I → a = 0 ∧ b = 0) :
    AlgebraicIndependent ℂ (fun i : Fin 2 => Ideal.Quotient.mk I (X (e i))) := by
  rw [algebraicIndependent_iff]
  intro F hF
  apply binary_rename_eq_zero_of_mem e hI hhom hlin
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have heq : (Ideal.Quotient.mkₐ ℂ I).comp (rename e) =
      aeval (fun i : Fin 2 => Ideal.Quotient.mk I (X (e i))) := by
    ext i
    simp
  exact (congrArg (fun f : BinaryForm →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ I) => f F) heq).trans hF

end Nagata.W02

end
end

section

namespace Nagata.W02
open Nagata.W04.ReducibleSquare

theorem lineRestriction_natDegree_le {K : Type*} [Field K]
    (i : K) (P : MvPolynomial (Fin 3) K) (d : ℕ) (hP : P.IsHomogeneous d) :
    (lineRestriction i P).natDegree ≤ d :=
  (lineRestriction_natDegree_le_totalDegree i P).trans hP.totalDegree_le

end Nagata.W02

end

end OAI
