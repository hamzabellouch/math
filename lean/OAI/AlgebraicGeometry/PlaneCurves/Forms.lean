import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import OAI.AlgebraicGeometry.PlaneCurves.PolynomialAvoidance

namespace OAI

/-!
# Homogeneous polynomial forms and dehomogenization
-/

section

/-!
# Nonzero homogeneous plane forms and products

The polynomial part of the permutation-product and common-multiple
constructions in manuscript §1, Lemma `lem:universal`.
-/

noncomputable section

namespace Nagata.W16

abbrev PlanePolynomial := MvPolynomial (Fin 3) ℂ

/-- Homogeneous scaling after an arbitrary coefficient-ring map. This version
also applies to evaluations in localizations of affine coordinate rings. -/
theorem homogeneous_eval₂_scale {σ K R : Type*} [CommSemiring K] [CommSemiring R]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d)
    (k : K →+* R) (x : σ → R) (a : R) :
    MvPolynomial.eval₂ k (fun i => a * x i) F =
      a ^ d * MvPolynomial.eval₂ k x F := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hF.degree_eq_sum_deg_support hu]
  ac_rfl

/-- Homogeneity gives the representative scaling law needed to descend a
homogeneous zero locus from nonzero vectors to projective points. -/
theorem homogeneous_eval_scale {σ K : Type*} [CommSemiring K]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d)
    (x : σ → K) (a : K) :
    MvPolynomial.eval (fun i => a * x i) F = a ^ d * MvPolynomial.eval x F := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hF.degree_eq_sum_deg_support hu]
  ac_rfl

/-- Vanishing of a homogeneous equation is invariant under nonzero rescaling
of its representative. -/
theorem homogeneous_eval_scale_eq_zero_iff {σ K : Type*} [CommRing K]
    [IsDomain K] {F : MvPolynomial σ K} {d : ℕ}
    (hF : F.IsHomogeneous d) (x : σ → K) {a : K} (ha : a ≠ 0) :
    MvPolynomial.eval (fun i => a * x i) F = 0 ↔ MvPolynomial.eval x F = 0 := by
  rw [homogeneous_eval_scale hF x a]
  simp only [mul_eq_zero, pow_ne_zero d ha, false_or]

/-- A nonzero degree-`d` homogeneous ternary complex polynomial.  Nonreduced
and reducible equations are allowed. -/
structure NonzeroHomogeneousForm (d : ℕ) where
  polynomial : PlanePolynomial
  homogeneous : polynomial.IsHomogeneous d
  nonzero : polynomial ≠ 0

namespace NonzeroHomogeneousForm

theorem totalDegree_eq {d : ℕ} (F : NonzeroHomogeneousForm d) :
    F.polynomial.totalDegree = d :=
  F.homogeneous.totalDegree F.nonzero

/-- A nonzero equation over `ℂ` cannot vanish at every affine vector. -/
theorem exists_eval_ne_zero {d : ℕ} (F : NonzeroHomogeneousForm d) :
    ∃ x : Fin 3 → ℂ, MvPolynomial.eval x F.polynomial ≠ 0 := by
  classical
  by_contra h
  apply F.nonzero
  apply F.homogeneous.eq_zero_of_forall_eval_eq_zero
  intro x
  by_contra hx
  exact h ⟨x, hx⟩

/-- Positive-degree homogeneous equations vanish at the zero vector. -/
theorem eval_zero_of_degree_pos {d : ℕ} (F : NonzeroHomogeneousForm d)
    (hd : 0 < d) : MvPolynomial.eval (0 : Fin 3 → ℂ) F.polynomial = 0 := by
  have h := homogeneous_eval_scale F.homogeneous (0 : Fin 3 → ℂ) (0 : ℂ)
  simpa [hd.ne'] using h

/-- A positive-degree nonzero equation has a nonzero vector outside its zero
locus, providing the representative needed for projective properness. -/
theorem exists_nonzero_vector_eval_ne_zero {d : ℕ}
    (F : NonzeroHomogeneousForm d) (hd : 0 < d) :
    ∃ x : Fin 3 → ℂ, x ≠ 0 ∧ MvPolynomial.eval x F.polynomial ≠ 0 := by
  obtain ⟨x, hx⟩ := F.exists_eval_ne_zero
  refine ⟨x, ?_, hx⟩
  intro hxzero
  subst x
  exact hx (F.eval_zero_of_degree_pos hd)

/-- Multiplying equations adds degrees and preserves nonzeroness. -/
def mul {d e : ℕ} (F : NonzeroHomogeneousForm d)
    (G : NonzeroHomogeneousForm e) : NonzeroHomogeneousForm (d + e) where
  polynomial := F.polynomial * G.polynomial
  homogeneous := F.homogeneous.mul G.homogeneous
  nonzero := mul_ne_zero F.nonzero G.nonzero

/-- Taking a power multiplies the degree, including the zeroth power. -/
def pow {d : ℕ} (F : NonzeroHomogeneousForm d) (N : ℕ) :
    NonzeroHomogeneousForm (d * N) where
  polynomial := F.polynomial ^ N
  homogeneous := F.homogeneous.pow N
  nonzero := pow_ne_zero N F.nonzero

theorem mul_totalDegree {d e : ℕ} (F : NonzeroHomogeneousForm d)
    (G : NonzeroHomogeneousForm e) :
    (F.polynomial * G.polynomial).totalDegree = d + e :=
  (F.mul G).totalDegree_eq

theorem pow_totalDegree {d : ℕ} (F : NonzeroHomogeneousForm d) (N : ℕ) :
    (F.polynomial ^ N).totalDegree = d * N :=
  (F.pow N).totalDegree_eq

end NonzeroHomogeneousForm

open scoped BigOperators

/-- A finite product of nonzero forms has the sum of the prescribed degrees.
The finite set may be empty, in which case the product is the constant one. -/
theorem finite_product_forms {ι : Type*} (s : Finset ι)
    (F : ι → PlanePolynomial) (d : ι → ℕ)
    (hhom : ∀ i ∈ s, (F i).IsHomogeneous (d i))
    (hne : ∀ i ∈ s, F i ≠ 0) :
    (∏ i ∈ s, F i) ≠ 0 ∧
      (∏ i ∈ s, F i).IsHomogeneous (∑ i ∈ s, d i) ∧
      (∏ i ∈ s, F i).totalDegree = ∑ i ∈ s, d i := by
  classical
  have hp : (∏ i ∈ s, F i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hh := MvPolynomial.IsHomogeneous.prod s F d hhom
  exact ⟨hp, hh, hh.totalDegree hp⟩

/-- Equal-degree product formula needed for the permutation product. -/
theorem finite_product_equal_degree {ι : Type*} (s : Finset ι)
    (F : ι → PlanePolynomial) (d : ℕ)
    (hhom : ∀ i ∈ s, (F i).IsHomogeneous d)
    (hne : ∀ i ∈ s, F i ≠ 0) :
    (∏ i ∈ s, F i) ≠ 0 ∧
      (∏ i ∈ s, F i).totalDegree = s.card * d := by
  have h := finite_product_forms s F (fun _ => d) hhom hne
  exact ⟨h.1, by simpa using h.2.2⟩

/-- The permutation product in §1 is a nonzero equation of degree `r! * d`.
Each factor can be chosen independently; no symmetry of its coefficients is
required. -/
theorem permutation_product_degree (r d : ℕ)
    (F : Equiv.Perm (Fin r) → PlanePolynomial)
    (hhom : ∀ σ, (F σ).IsHomogeneous d) (hne : ∀ σ, F σ ≠ 0) :
    (∏ σ, F σ) ≠ 0 ∧
      (∏ σ, F σ).totalDegree = Nat.factorial r * d := by
  classical
  simpa [Fintype.card_perm] using
    finite_product_equal_degree Finset.univ F d (fun σ _ => hhom σ)
      (fun σ _ => hne σ)

end Nagata.W16

end
end

section

/-! Binary homogeneous equations on `[U:Z]`, restricted to `Z=1`. -/

noncomputable section

namespace Nagata.W16

open scoped BigOperators

def binaryAffine (F : MvPolynomial (Fin 2) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun i => if i = 0 then Polynomial.X else 1) F

theorem binaryAffine_eq_sum (F : MvPolynomial (Fin 2) ℂ) :
    binaryAffine F = ∑ u ∈ F.support, Polynomial.C (F.coeff u) * Polynomial.X ^ u 0 := by
  classical
  rw [binaryAffine, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro u _
  simp

theorem binaryAffine_eval (F : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    (binaryAffine F).eval z = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else 1) F := by
  classical
  simp [binaryAffine_eq_sum, MvPolynomial.eval_eq', Polynomial.eval_finsetSum]

theorem binaryAffine_normalized {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (x : Fin 2 → ℂ) (hc : x 1 ≠ 0) :
    (binaryAffine F).eval (x 0 / x 1) = (x 1)⁻¹ ^ d * MvPolynomial.eval x F := by
  rw [binaryAffine_eval]
  have hcoords : (fun i : Fin 2 => if i = 0 then x 0 / x 1 else 1) =
      fun i => (x 1)⁻¹ * x i := by
    funext i
    fin_cases i <;> simp [hc, div_eq_mul_inv, mul_comm]
  rw [hcoords]
  exact homogeneous_eval_scale hF x (x 1)⁻¹

theorem binaryAffine_eq_zero_imp {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hf : binaryAffine F = 0) : F = 0 := by
  have hmul : MvPolynomial.X 1 * F = 0 := by
    apply ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).mul hF).eq_zero_of_forall_eval_eq_zero
    intro x
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    by_cases hc : x 1 = 0
    · simp [hc]
    · have hval := binaryAffine_normalized hF x hc
      rw [hf, Polynomial.eval_zero] at hval
      have hz : MvPolynomial.eval x F = 0 :=
        (mul_eq_zero.mp hval.symm).resolve_left (pow_ne_zero d (inv_ne_zero hc))
      rw [hz, mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_left (MvPolynomial.X_ne_zero 1)

theorem binaryAffine_ne_zero {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hf : F ≠ 0) : binaryAffine F ≠ 0 := by
  intro hz
  exact hf (binaryAffine_eq_zero_imp hF hz)

theorem binaryAffine_natDegree_le {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) : (binaryAffine F).natDegree ≤ d := by
  classical
  rw [binaryAffine_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  apply (Polynomial.natDegree_C_mul_X_pow_le (F.coeff u) (u 0)).trans
  rw [hF.degree_eq_sum_deg_support hu]
  by_cases hz : u 0 = 0
  · simp [hz]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hz)

end Nagata.W16

end
end

section

/-!
# Faithfulness of affine chart equations

The fixed-degree homogeneous equation of a plane curve is determined by its
restriction to any one ordinary projective affine chart. The proof uses
polynomial function extensionality over the infinite field `ℂ`; no analytic
or scheme-theoretic density assertion is assumed.
-/

namespace Nagata.W16

open Nagata.ProjectiveGeometry

theorem eval_dehomogenize (c : Fin 3) (F : PlanePolynomial)
    (x : ChartVariables c → ℂ) :
    MvPolynomial.eval x (dehomogenize c F) =
      MvPolynomial.eval (fun j => if h : j = c then 1 else x ⟨j, h⟩) F := by
  classical
  unfold dehomogenize
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun z : Fin 3 → ℂ => MvPolynomial.eval z F)
  funext j
  by_cases h : j = c <;> simp [h, Function.comp_apply]

/-- The affine chart evaluation formula has its exact homogeneous scaling
factor, with no division performed at a zero chart coordinate. -/
theorem eval_dehomogenize_normalized {d : ℕ} {F : PlanePolynomial}
    (hF : F.IsHomogeneous d) (c : Fin 3) (x : Fin 3 → ℂ) (hc : x c ≠ 0) :
    MvPolynomial.eval (fun j : ChartVariables c => x j.val / x c)
        (dehomogenize c F) =
      (x c)⁻¹ ^ d * MvPolynomial.eval x F := by
  classical
  rw [eval_dehomogenize]
  have hcoords :
      (fun j : Fin 3 => if h : j = c then (1 : ℂ) else x j / x c) =
        fun j => (x c)⁻¹ * x j := by
    funext j
    by_cases h : j = c
    · subst j
      simp [hc]
    · simp [h, div_eq_mul_inv, mul_comm]
  rw [hcoords]
  exact homogeneous_eval_scale hF x (x c)⁻¹

theorem eval_eq_zero_of_dehomogenize_eq_zero {d : ℕ} {F : PlanePolynomial}
    (hF : F.IsHomogeneous d) (c : Fin 3) (hchart : dehomogenize c F = 0)
    (x : Fin 3 → ℂ) (hc : x c ≠ 0) : MvPolynomial.eval x F = 0 := by
  have hz := congrArg
    (MvPolynomial.eval (fun j : ChartVariables c => x j.val / x c)) hchart
  rw [eval_dehomogenize_normalized hF c x hc, map_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero d (inv_ne_zero hc))

/-- A homogeneous equation whose restriction to one affine chart is zero is
the zero polynomial. Multiplication by the distinguished coordinate handles
vectors on the omitted hyperplane. -/
theorem eq_zero_of_dehomogenize_eq_zero {d : ℕ} {F : PlanePolynomial}
    (hF : F.IsHomogeneous d) (c : Fin 3) (hchart : dehomogenize c F = 0) : F = 0 := by
  have hmul : MvPolynomial.X c * F = 0 := by
    apply ((MvPolynomial.isHomogeneous_X ℂ c).mul hF).eq_zero_of_forall_eval_eq_zero
    intro x
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    by_cases hc : x c = 0
    · simp [hc]
    · rw [eval_eq_zero_of_dehomogenize_eq_zero hF c hchart x hc, mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_left (MvPolynomial.X_ne_zero c)

theorem dehomogenize_ne_zero {d : ℕ} {F : PlanePolynomial}
    (hF : F.IsHomogeneous d) (hne : F ≠ 0) (c : Fin 3) :
    dehomogenize c F ≠ 0 := by
  intro hz
  exact hne (eq_zero_of_dehomogenize_eq_zero hF c hz)

/-- Affine restriction is injective on each fixed homogeneous degree. -/
theorem dehomogenize_injective_fixed_degree {d : ℕ} {F G : PlanePolynomial}
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d) (c : Fin 3)
    (hchart : dehomogenize c F = dehomogenize c G) : F = G := by
  apply sub_eq_zero.mp
  apply eq_zero_of_dehomogenize_eq_zero (hF.sub hG) c
  change MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* MvPolynomial (ChartVariables c) ℂ)
    (fun j : Fin 3 => if h : j = c then 1 else MvPolynomial.X ⟨j, h⟩) (F - G) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hchart

end Nagata.W16

end

section

/-!
# Faithfulness of the simultaneous affine chart in a product of planes

This is the multihomogeneous extension of single-plane dehomogenization.
The affine chart uses exactly `Fin r × Fin 2` coordinates. In particular,
no product-topology replacement for the product's Zariski geometry is used.
-/

noncomputable section

namespace Nagata.W16

open Nagata.ProjectiveGeometry
open scoped BigOperators

/-- Restrict every point block to `[1 : z₀ : z₁]`. -/
def blockDehomogenize {r : ℕ} (F : MultihomogeneousEquation r) :
    MvPolynomial (Fin r × Fin 2) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun ij => if ij.2 = 0 then 1 else
      if ij.2 = 1 then MvPolynomial.X (ij.1, 0) else MvPolynomial.X (ij.1, 1))
    F.polynomial

/-- Independent rescaling of the point blocks gives the multidegree factor. -/
theorem multihomogeneous_eval_scale {r : ℕ} (F : MultihomogeneousEquation r)
    (x : Fin r × Fin 3 → ℂ) (a : Fin r → ℂ) :
    MvPolynomial.eval (fun ij => a ij.1 * x ij) F.polynomial =
      (∏ i, a i ^ F.multidegree i) * MvPolynomial.eval x F.polynomial := by
  classical
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hdegrees : (∏ ij : Fin r × Fin 3, a ij.1 ^ u ij) =
      ∏ i, a i ^ F.multidegree i := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ y : Fin 3, a i ^ u (i, y)) = a i ^ F.multidegree i
    rw [Finset.prod_pow_eq_pow_sum, F.homogeneous u hu i]
  rw [hdegrees]
  ac_rfl

theorem eval_blockDehomogenize {r : ℕ} (F : MultihomogeneousEquation r)
    (x : Fin r × Fin 2 → ℂ) :
    MvPolynomial.eval x (blockDehomogenize F) =
      MvPolynomial.eval
        (fun ij => affinePlaneVector (fun j => x (ij.1, j)) ij.2) F.polynomial := by
  classical
  unfold blockDehomogenize
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun z : Fin r × Fin 3 → ℂ => MvPolynomial.eval z F.polynomial)
  funext ij
  rcases ij with ⟨i, j⟩
  fin_cases j <;> simp [affinePlaneVector, Function.comp_apply]

theorem eval_blockDehomogenize_normalized {r : ℕ} (F : MultihomogeneousEquation r)
    (x : Fin r × Fin 3 → ℂ) (hc : ∀ i, x (i, 0) ≠ 0) :
    MvPolynomial.eval (fun ij : Fin r × Fin 2 => x (ij.1, ij.2.succ) / x (ij.1, 0))
        (blockDehomogenize F) =
      (∏ i, (x (i, 0))⁻¹ ^ F.multidegree i) * MvPolynomial.eval x F.polynomial := by
  classical
  rw [eval_blockDehomogenize]
  have hcoords :
      (fun ij : Fin r × Fin 3 =>
        affinePlaneVector (fun j => x (ij.1, j.succ) / x (ij.1, 0)) ij.2) =
      fun ij => (x (ij.1, 0))⁻¹ * x ij := by
    funext ij
    rcases ij with ⟨i, j⟩
    fin_cases j <;> simp [affinePlaneVector, hc i, div_eq_mul_inv] <;> ac_rfl
  rw [hcoords]
  exact multihomogeneous_eval_scale F x (fun i => (x (i, 0))⁻¹)

/-- A zero simultaneous affine restriction forces the multihomogeneous
polynomial itself to vanish. -/
theorem eq_zero_of_blockDehomogenize_eq_zero {r : ℕ}
    (F : MultihomogeneousEquation r) (hchart : blockDehomogenize F = 0) :
    F.polynomial = 0 := by
  classical
  let Q : MvPolynomial (Fin r × Fin 3) ℂ := ∏ i : Fin r, MvPolynomial.X (i, 0)
  have hQ : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact MvPolynomial.X_ne_zero (i, 0)
  have hmul : Q * F.polynomial = 0 := by
    apply Nagata.Workers.W25.complex_polynomial_funext
    intro x
    rw [map_mul, map_zero]
    by_cases hc : ∀ i : Fin r, x (i, 0) ≠ 0
    · have hz := congrArg
        (MvPolynomial.eval (fun ij : Fin r × Fin 2 => x (ij.1, ij.2.succ) / x (ij.1, 0)))
        hchart
      rw [eval_blockDehomogenize_normalized F x hc, map_zero] at hz
      have hn : (∏ i, (x (i, 0))⁻¹ ^ F.multidegree i) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        exact pow_ne_zero _ (inv_ne_zero (hc i))
      rw [(mul_eq_zero.mp hz).resolve_left hn, mul_zero]
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hc
      have hi0 : x (i, 0) = 0 := Classical.not_not.mp hi
      have heval : MvPolynomial.eval x Q = ∏ i : Fin r, x (i, 0) := by
        simp [Q]
      rw [heval, Finset.prod_eq_zero (Finset.mem_univ i) hi0, zero_mul]
  exact (mul_eq_zero.mp hmul).resolve_left hQ

/-- Every nonzero multihomogeneous equation stays nonzero on the standard
simultaneous affine chart. -/
theorem blockDehomogenize_ne_zero {r : ℕ} (F : MultihomogeneousEquation r)
    (hne : F.polynomial ≠ 0) : blockDehomogenize F ≠ 0 := by
  intro hz
  exact hne (eq_zero_of_blockDehomogenize_eq_zero F hz)

end Nagata.W16

end
end

end OAI
