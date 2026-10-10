import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalQuotientEquiv

namespace OAI

namespace SiegelZeros


open scoped BigOperators

namespace WeightedTorusJets

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

noncomputable def homogeneousDeformation (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    MvPolynomial σ (Polynomial R) :=
  homogeneousComponent d (polynomialDeformation f d i)

theorem map_homogeneousComponent (φ : R →+* S) (n : ℕ) (f : MvPolynomial σ R) :
    map φ (homogeneousComponent n f) = homogeneousComponent n (map φ f) := by
  ext a
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

theorem polynomialDeformation_at_one (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    map (Polynomial.evalRingHom 1) (polynomialDeformation f d i) = X i ^ d := by
  simp [polynomialDeformation]

theorem homogeneousDeformation_at_one (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    map (Polynomial.evalRingHom 1) (homogeneousDeformation f d i) = X i ^ d := by
  rw [homogeneousDeformation, map_homogeneousComponent, polynomialDeformation_at_one]
  simp [homogeneousComponent_of_mem (isHomogeneous_X_pow i d)]

noncomputable def macaulayColumn (d n : ℕ) (G : σ → MvPolynomial σ R)
    (hG : ∀ i, (G i).IsHomogeneous d)
    (b : σ × {b : σ →₀ ℕ // b.degree + d = n}) : homogeneousSubmodule σ R n :=
  ⟨monomial b.2.1 1 * G b.1, by
    change (monomial b.2.1 (1 : R) * G b.1).IsHomogeneous n
    simpa only [b.2.2] using
      (isHomogeneous_monomial (d := b.2.1) (1 : R) rfl).mul (hG b.1)⟩

noncomputable def macaulayMap (d n : ℕ) (G : σ → MvPolynomial σ R)
    (hG : ∀ i, (G i).IsHomogeneous d) :
    ((σ × {b : σ →₀ ℕ // b.degree + d = n}) →₀ R) →ₗ[R]
      homogeneousSubmodule σ R n :=
  Finsupp.linearCombination R (macaulayColumn d n G hG)

noncomputable def macaulayMatrix (d n : ℕ) (G : σ → MvPolynomial σ R) :
    Matrix {a : σ →₀ ℕ // a.degree = n}
      (σ × {b : σ →₀ ℕ // b.degree + d = n}) R :=
  fun a b => (monomial b.2.1 1 * G b.1).coeff a.1

theorem macaulayMatrix_map (φ : R →+* S) (d n : ℕ) (G : σ → MvPolynomial σ R) :
    (macaulayMatrix d n G).map φ = macaulayMatrix d n (fun i => map φ (G i)) := by
  ext a b
  change φ ((monomial b.2.1 1 * G b.1).coeff a.1) =
    (monomial b.2.1 1 * map φ (G b.1)).coeff a.1
  rw [← coeff_map]
  simp

theorem deformed_macaulay_at_one (f : σ → MvPolynomial σ R) (d n : ℕ) :
    (macaulayMatrix d n (homogeneousDeformation f d)).map (Polynomial.evalRingHom 1) =
      macaulayMatrix d n (fun i => (X i : MvPolynomial σ R) ^ d) := by
  rw [macaulayMatrix_map]
  simp only [homogeneousDeformation_at_one]

end WeightedTorusJets

open Module

namespace WeightedTorusJets

@[instance_reducible] noncomputable def monomialDegreeFintype (σ : Type*) [Finite σ] (n : ℕ) :
    Fintype {m : σ →₀ ℕ // m.degree = n} :=
  (Finsupp.finite_of_degree_eq n).fintype

@[instance_reducible] noncomputable def monomialSourceFintype (σ : Type*) [Finite σ] (n d : ℕ) :
    Fintype {m : σ →₀ ℕ // m.degree + d = n} :=
  ((Finsupp.finite_of_degree_le n).subset (fun m hm => by
    change m.degree + d = n at hm
    change m.degree ≤ n
    omega)).fintype

noncomputable def homogeneousMonomialBasis (σ R : Type*) [CommSemiring R] (n : ℕ) :
    Basis {m : σ →₀ ℕ // m.degree = n} R (MvPolynomial.homogeneousSubmodule σ R n) :=
  (MvPolynomial.basisRestrictSupport R {m : σ →₀ ℕ | m.degree = n}).map
    (LinearEquiv.ofEq _ _
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := σ) (R := R) n).symm)

end WeightedTorusJets

open MvPolynomial

noncomputable section

namespace WeightedTorusJets.Geometry.GradedQuotient

variable {K σ : Type*} [Field K]

def degreePiece (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  (homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap

def degreePresentation (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    homogeneousSubmodule σ K n →ₗ[K] degreePiece I n :=
  (Ideal.Quotient.mkₐ K I).toLinearMap.submoduleMap (homogeneousSubmodule σ K n)

theorem degreePresentation_surjective (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Function.Surjective (degreePresentation I n) :=
  (Ideal.Quotient.mkₐ K I).toLinearMap.submoduleMap_surjective _

theorem ker_degreePresentation (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    LinearMap.ker (degreePresentation I n) =
      (I.restrictScalars K).comap (homogeneousSubmodule σ K n).subtype := by
  change LinearMap.ker (((I.restrictScalars K).mkQ).submoduleMap
    (homogeneousSubmodule σ K n)) = _
  rw [LinearMap.ker_submoduleMap, Submodule.ker_mkQ]

theorem finrank_degreePiece_eq_sub_finrank_range [Finite σ]
    {V : Type*} [AddCommGroup V] [Module K V]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (m : V →ₗ[K] homogeneousSubmodule σ K n)
    (hrange : LinearMap.range m =
      (I.restrictScalars K).comap (homogeneousSubmodule σ K n).subtype) :
    Module.finrank K (degreePiece I n) =
      Module.finrank K (homogeneousSubmodule σ K n) - Module.finrank K (LinearMap.range m) := by
  let : Module.Finite K (homogeneousSubmodule σ K n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg σ K n)
  have h := (degreePresentation I n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (degreePresentation_surjective I n), finrank_top,
    ker_degreePresentation, ← hrange] at h
  omega

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient
variable {K σ : Type*} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
theorem homogeneousComponent_mul_of_le {f g : MvPolynomial σ K} {d n : ℕ}
    (hf : f.IsHomogeneous d) (hdn : d ≤ n) :
    homogeneousComponent n (f * g) = f * homogeneousComponent (n - d) g := by
  have h := DirectSum.coe_decompose_mul_of_left_mem_of_le
    (homogeneousSubmodule σ K) (b := g) hf hdn
  change (decomposition.decompose' (f * g) n : MvPolynomial σ K) =
    f * (decomposition.decompose' g (n - d) : MvPolynomial σ K) at h
  simpa only [decomposition.decompose'_apply] using h

theorem homogeneousComponent_mul_of_lt {f g : MvPolynomial σ K} {d n : ℕ}
    (hf : f.IsHomogeneous d) (hnd : n < d) :
    homogeneousComponent n (f * g) = 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem_of_not_le
    (homogeneousSubmodule σ K) (b := g) hf (Nat.not_le.mpr hnd)
  change (decomposition.decompose' (f * g) n : MvPolynomial σ K) = 0 at h
  simpa only [decomposition.decompose'_apply] using h

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets

open MvPolynomial

theorem macaulayMap_range_eq_ideal_slice {σ K : Type*} [Fintype σ] [Field K]
    (d n : ℕ) (G : σ → MvPolynomial σ K) (hG : ∀ i, (G i).IsHomogeneous d) :
    LinearMap.range (macaulayMap d n G hG) =
      ((Ideal.span (Set.range G)).restrictScalars K).comap
        (homogeneousSubmodule σ K n).subtype := by
  classical
  let T := LinearMap.range (macaulayMap d n G hG)
  let J := T.map (homogeneousSubmodule σ K n).subtype
  have hJ (b : σ × {b : σ →₀ ℕ // b.degree + d = n}) :
      monomial b.2.1 1 * G b.1 ∈ J := by
    refine ⟨macaulayColumn d n G hG b, ?_, rfl⟩
    exact ⟨Finsupp.single b 1, by simp [macaulayMap]⟩
  apply le_antisymm
  · rw [macaulayMap, Finsupp.range_linearCombination]
    apply Submodule.span_le.mpr
    rintro p ⟨b, rfl⟩
    change monomial b.2.1 1 * G b.1 ∈ Ideal.span (Set.range G)
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b.1, rfl⟩)
  · intro p hp
    change (p : MvPolynomial σ K) ∈ Ideal.span (Set.range G) at hp
    obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    have hmul (i : σ) : homogeneousComponent n (g i * G i) ∈ J := by
      by_cases hdn : d ≤ n
      · rw [mul_comm (g i) (G i),
          Geometry.GradedQuotient.homogeneousComponent_mul_of_le (hG i) hdn,
          mul_comm (G i)]
        let a := homogeneousComponent (n - d) (g i)
        change a * G i ∈ J
        rw [a.as_sum, Finset.sum_mul]
        apply J.sum_mem
        intro b hb
        have hbdeg : b.degree = n - d :=
          (Finsupp.degree_apply b).trans
            ((homogeneousComponent_isHomogeneous (n - d) (g i)).degree_eq_sum_deg_support hb).symm
        have hbnd : b.degree + d = n := by omega
        simpa only [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one] using
          J.smul_mem (a.coeff b) (hJ (i, ⟨b, hbnd⟩))
      · rw [mul_comm (g i) (G i),
          Geometry.GradedQuotient.homogeneousComponent_mul_of_lt (hG i)
            (Nat.lt_of_not_ge hdn)]
        exact J.zero_mem
    have hpJ : (p : MvPolynomial σ K) ∈ J := by
      rw [← homogeneousComponent_eq_self p.property, ← hg, map_sum]
      exact J.sum_mem fun i _ => hmul i
    obtain ⟨p', hp', hpp⟩ := hpJ
    have hpp' : p' = p := Subtype.ext hpp
    rwa [hpp'] at hp'

end WeightedTorusJets

namespace WeightedTorusJets

open MvPolynomial Geometry.GradedQuotient

theorem toMatrix_macaulayMap {σ K : Type*} [Fintype σ] [Field K]
    (d n : ℕ) (G : σ → MvPolynomial σ K) (hG : ∀ i, (G i).IsHomogeneous d)
    [Fintype {a : σ →₀ ℕ // a.degree = n}]
    [Fintype {b : σ →₀ ℕ // b.degree + d = n}]
    [DecidableEq (σ × {b : σ →₀ ℕ // b.degree + d = n})] :
    LinearMap.toMatrix Finsupp.basisSingleOne (homogeneousMonomialBasis σ K n)
      (macaulayMap d n G hG) = macaulayMatrix d n G := by
  ext a b
  simp only [macaulayMap, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
    Finsupp.linearCombination_single, one_smul]
  rfl

theorem macaulayMatrix_rank_eq_finrank_range {σ K : Type*} [Fintype σ] [Field K]
    (d n : ℕ) (G : σ → MvPolynomial σ K) (hG : ∀ i, (G i).IsHomogeneous d)
    [Fintype {a : σ →₀ ℕ // a.degree = n}]
    [Fintype {b : σ →₀ ℕ // b.degree + d = n}] :
    (macaulayMatrix d n G).rank = Module.finrank K (LinearMap.range (macaulayMap d n G hG)) := by
  classical
  rw [← toMatrix_macaulayMap d n G hG]
  rw [Matrix.rank_eq_finrank_range_toLin _ (homogeneousMonomialBasis σ K n)
    Finsupp.basisSingleOne, Matrix.toLin_toMatrix]

theorem finrank_degreePiece_span_eq_sub_macaulayMatrix_rank
    {σ K : Type*} [Fintype σ] [Field K]
    (d n : ℕ) (G : σ → MvPolynomial σ K) (hG : ∀ i, (G i).IsHomogeneous d)
    [Fintype {a : σ →₀ ℕ // a.degree = n}]
    [Fintype {b : σ →₀ ℕ // b.degree + d = n}] :
    Module.finrank K (degreePiece (Ideal.span (Set.range G)) n) =
      Module.finrank K (homogeneousSubmodule σ K n) - (macaulayMatrix d n G).rank := by
  rw [finrank_degreePiece_eq_sub_finrank_range _ _ _
    (macaulayMap_range_eq_ideal_slice d n G hG),
    macaulayMatrix_rank_eq_finrank_range d n G hG]

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

theorem exists_row_minor_det_ne_zero {K ι n : Type*} [Field K]
    [Fintype n] [DecidableEq n] (v : ι → n → K)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ e : n → ι, Function.Injective e ∧ Matrix.det (fun i j => v (e i) j) ≠ 0 := by
  classical
  obtain ⟨b, hbmem, _, hbli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range v)
  choose f hf using hbmem
  have hk : Module.finrank K (Submodule.span K (Set.range v)) = Fintype.card n := by
    rw [hv, finrank_top, Module.finrank_pi]
  let e₀ : n ≃ Fin (Module.finrank K (Submodule.span K (Set.range v))) :=
    Fintype.equivFinOfCardEq hk.symm
  let e : n → ι := f ∘ e₀
  have he : (fun i => v (e i)) = b ∘ e₀ := by
    funext i
    exact hf (e₀ i)
  have hrow : LinearIndependent K (fun i => v (e i)) := by
    rw [he]
    exact hbli.comp e₀ e₀.injective
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    exact hrow.injective (congrArg v hij)
  · exact isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrow))

theorem exists_rank_minor {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n), (A.submatrix r c).det ≠ 0 := by
  classical
  rw [A.rank_eq_finrank_span_row]
  obtain ⟨b, hbmem, _, hbli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  choose r hr using hbmem
  let B := A.submatrix r id
  have hrow : LinearIndependent K B.row := by
    have he : B.row = b := by
      funext i
      exact hr i
    rw [he]
    exact hbli
  have hspan : Submodule.span K (Set.range B.transpose.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, Matrix.rank_transpose, hrow.rank_matrix,
      Module.finrank_pi]
  obtain ⟨c, _, hc⟩ := exists_row_minor_det_ne_zero B.transpose.row hspan
  refine ⟨r, c, ?_⟩
  have he : (fun i j => B.transpose.row (c i) j) = (A.submatrix r c).transpose := rfl
  rwa [he, Matrix.det_transpose] at hc

theorem rank_specialization_le {R K L m n : Type*}
    [CommRing R] [Field K] [Field L] [Fintype m] [Fintype n]
    (φ : R →+* K) (ψ : R →+* L) (hψ : Function.Injective ψ) (A : Matrix m n R) :
    (A.map φ).rank ≤ (A.map ψ).rank := by
  classical
  obtain ⟨r, c, hc⟩ := exists_rank_minor (A.map φ)
  have hφ : φ ((A.submatrix r c).det) ≠ 0 := by
    rw [φ.map_det]
    exact hc
  have hdet : (A.submatrix r c).det ≠ 0 := by
    intro h
    exact hφ (by rw [h, map_zero])
  have hψdet : ψ ((A.submatrix r c).det) ≠ 0 := by
    exact fun h => hdet (hψ (h.trans (map_zero ψ).symm))
  have hminor : ((A.map ψ).submatrix r c).det ≠ 0 := by
    change (ψ.mapMatrix (A.submatrix r c)).det ≠ 0
    rw [← ψ.map_det]
    exact hψdet
  have heq := Matrix.rank_of_det_ne_zero hminor
  simpa only [Fintype.card_fin] using
    heq.symm.le.trans (Matrix.rank_submatrix_le (A.map ψ) r c)

theorem rank_polynomial_eval_le {K m n : Type*} [Field K]
    [Fintype m] [Fintype n] (A : Matrix m n (Polynomial K)) (a : K) :
    (A.map (Polynomial.evalRingHom a)).rank ≤
      (A.map (algebraMap (Polynomial K) (RatFunc K))).rank :=
  rank_specialization_le _ _ (RatFunc.algebraMap_injective K) A



theorem finrank_homogeneousSubmodule {σ K : Type*} [Fintype σ] [Field K] (n : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K n) =
      (Fintype.card σ + n - 1).choose n := by
  classical
  let e : Sym σ n ≃ {d : σ →₀ ℕ // d.degree = n} := Sym.equivNatSum σ n
  let : Fintype {d : σ →₀ ℕ // d.degree = n} := Fintype.ofEquiv (Sym σ n) e
  rw [Module.finrank_eq_card_basis (WeightedTorusJets.homogeneousMonomialBasis σ K n)]
  exact (Fintype.card_congr e).symm.trans (Sym.card_sym_eq_choose n)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

open MvPolynomial

theorem deformed_macaulay_generic_rank_ge
    {σ K : Type*} [Field K] [Fintype σ]
    (f : σ → MvPolynomial σ K) (d n : ℕ)
    [Fintype {a : σ →₀ ℕ // a.degree = n}]
    [Fintype {b : σ →₀ ℕ // b.degree + d = n}] :
    (macaulayMatrix d n (fun i => (X i : MvPolynomial σ K) ^ d)).rank ≤
      (macaulayMatrix d n (fun i =>
        map (algebraMap (Polynomial K) (RatFunc K))
          (homogeneousDeformation f d i))).rank := by
  have h := Geometry.rank_polynomial_eval_le
    (macaulayMatrix d n (homogeneousDeformation f d)) (1 : K)
  rwa [deformed_macaulay_at_one, macaulayMatrix_map] at h

end WeightedTorusJets
namespace WeightedTorusJets

open MvPolynomial Geometry.GradedQuotient

theorem finrank_degreePiece_deformed_le_pure_powers
    {σ K : Type*} [Fintype σ] [Field K]
    (f : σ → MvPolynomial σ K) (d n : ℕ) :
    Module.finrank (RatFunc K)
        (degreePiece (Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K))
            (homogeneousDeformation f d i)))) n) ≤
      Module.finrank K
        (degreePiece (Ideal.span (Set.range (fun i => (X i : MvPolynomial σ K) ^ d))) n) := by
  let := monomialDegreeFintype σ n
  let := monomialSourceFintype σ n d
  have hG (i : σ) :
      (map (algebraMap (Polynomial K) (RatFunc K))
        (homogeneousDeformation f d i)).IsHomogeneous d :=
    (homogeneousComponent_isHomogeneous d (polynomialDeformation f d i)).map _
  rw [finrank_degreePiece_span_eq_sub_macaulayMatrix_rank d n _ hG,
    finrank_degreePiece_span_eq_sub_macaulayMatrix_rank d n _ (fun i => isHomogeneous_X_pow i d),
    Geometry.finrank_homogeneousSubmodule, Geometry.finrank_homogeneousSubmodule]
  exact Nat.sub_le_sub_left (deformed_macaulay_generic_rank_ge f d n) _

end WeightedTorusJets


open scoped BigOperators DirectSum
open MvPolynomial

namespace WeightedTorusJets.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneous_quotient_coeLinearMap_injective
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (N : ℕ) :
    Function.Injective (DirectSum.coeLinearMap
      (fun i : Fin N => (homogeneousSubmodule σ K (i : ℕ)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap)) := by
  classical
  let A (i : Fin N) := (homogeneousSubmodule σ K (i : ℕ)).map
    (Ideal.Quotient.mkₐ K I).toLinearMap
  let q := Ideal.Quotient.mkₐ K I
  change Function.Injective (DirectSum.coeLinearMap A)
  suffices hk : ∀ x : ⨁ i, A i, DirectSum.coeLinearMap A x = 0 → x = 0 by
    intro x y hxy
    exact sub_eq_zero.mp (hk (x - y) (by simp only [map_sub, hxy, sub_self]))
  intro x hx
  have hxsum : (∑ i : Fin N, (x i : MvPolynomial σ K ⧸ I)) = 0 := by
    rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum,
      DFinsupp.sum_of_support_subset (Finset.subset_univ _) (fun _ _ => rfl)] at hx
    exact hx
  have hlift (i : Fin N) : ∃ p : MvPolynomial σ K,
      p ∈ homogeneousSubmodule σ K (i : ℕ) ∧ q p = (x i : MvPolynomial σ K ⧸ I) :=
    (x i).property
  choose p hp hpx using hlift
  have hsum : (∑ i, p i) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (∑ i, p i) = 0
    rw [map_sum]
    simpa only [hpx] using hxsum
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change (x i : MvPolynomial σ K ⧸ I) = 0
  rw [← hpx i]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmem := homogeneousComponent_mem_of_mem hI hsum (i : ℕ)
  have heq : homogeneousComponent (i : ℕ) (∑ j : Fin N, p j) = p i := by
    rw [map_sum]
    simp_rw [homogeneousComponent_of_mem (hp _)]
    simp [Fin.val_inj]
  rwa [heq] at hmem

open MvPolynomial
open scoped DirectSum

variable {K σ : Type*} [Field K] [Finite σ]

theorem quotient_finrank_le_sum_homogeneous_images
    (I : Ideal (MvPolynomial σ K)) (N : ℕ)
    (hzero : ∀ n, N ≤ n →
      (homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap = ⊥) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      Module.finrank K (MvPolynomial σ K ⧸ I) ≤
        ∑ i : Fin N, Module.finrank K
          ((homogeneousSubmodule σ K (i : ℕ)).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let A (i : Fin N) := (homogeneousSubmodule σ K (i : ℕ)).map q.toLinearMap
  have hfinite (i : Fin N) : Module.Finite K (A i) := by
    have : Module.Finite K (homogeneousSubmodule σ K (i : ℕ)) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K (i : ℕ))
    exact Module.Finite.map _ _
  have hspan : (⨆ i, A i) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective K I x
    change q f ∈ ⨆ i, A i
    rw [← sum_homogeneousComponent f, map_sum]
    apply Submodule.sum_mem
    intro n _
    by_cases hn : n < N
    · apply (le_iSup A ⟨n, hn⟩)
      exact Submodule.mem_map_of_mem (homogeneousComponent_mem n f)
    · have hz : q (homogeneousComponent n f) = 0 := by
        have hm := Submodule.mem_map_of_mem (f := q.toLinearMap) (homogeneousComponent_mem n f)
        rw [hzero n (Nat.le_of_not_gt hn)] at hm
        exact hm
      simpa only [hz] using (⨆ i, A i).zero_mem
  have hsurj : Function.Surjective (DirectSum.coeLinearMap A) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, hspan]
  have hfiniteQ := Module.Finite.of_surjective (DirectSum.coeLinearMap A) hsurj
  refine ⟨hfiniteQ, ?_⟩
  have heq := Module.finrank_directSum (R := K) (fun i : Fin N => A i)
  exact (LinearMap.finrank_le_finrank_of_surjective hsurj).trans_eq heq

theorem quotient_finrank_le_of_homogeneous_image_finrank_le
    {L τ : Type*} [Field L] [Finite τ]
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ L))
    (hJ : J.IsHomogeneous (homogeneousSubmodule τ L)) (N : ℕ)
    (hcut : ∀ n, N ≤ n →
      (homogeneousSubmodule τ L n).map (Ideal.Quotient.mkₐ L J).toLinearMap = ⊥)
    (hle : ∀ n, Module.finrank K
      ((homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank L
        ((homogeneousSubmodule τ L n).map (Ideal.Quotient.mkₐ L J).toLinearMap)) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      Module.finrank K (MvPolynomial σ K ⧸ I) ≤
        Module.finrank L (MvPolynomial τ L ⧸ J) := by
  classical
  have hfiniteI (n : ℕ) : Module.Finite K
      ((homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
    have : Module.Finite K (homogeneousSubmodule σ K n) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K n)
    exact Module.Finite.map _ _
  have hfiniteJ (n : ℕ) : Module.Finite L
      ((homogeneousSubmodule τ L n).map (Ideal.Quotient.mkₐ L J).toLinearMap) := by
    have : Module.Finite L (homogeneousSubmodule τ L n) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg τ L n)
    exact Module.Finite.map _ _
  have hcutI (n : ℕ) (hn : N ≤ n) :
      (homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hz := congrArg (fun V : Submodule L (MvPolynomial τ L ⧸ J) => Module.finrank L V)
      (hcut n hn)
    rw [finrank_bot] at hz
    exact Nat.eq_zero_of_le_zero ((hle n).trans_eq hz)
  obtain ⟨hIfin, hIbound⟩ := quotient_finrank_le_sum_homogeneous_images I N hcutI
  have : Module.Finite L (MvPolynomial τ L ⧸ J) :=
    (quotient_finrank_le_sum_homogeneous_images J N hcut).1
  have hsumJ : (∑ i : Fin N, Module.finrank L
      ((homogeneousSubmodule τ L (i : ℕ)).map (Ideal.Quotient.mkₐ L J).toLinearMap)) ≤
        Module.finrank L (MvPolynomial τ L ⧸ J) := by
    have hinj := homogeneous_quotient_coeLinearMap_injective J hJ N
    have heq := Module.finrank_directSum (R := L) (fun i : Fin N =>
      (homogeneousSubmodule τ L (i : ℕ)).map (Ideal.Quotient.mkₐ L J).toLinearMap)
    rw [← heq]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  refine ⟨hIfin, hIbound.trans ((Finset.sum_le_sum ?_).trans hsumJ)⟩
  intro i _
  exact hle i

open MvPolynomial

def rectangularIdeal {σ : Type u_1} {K : Type u_2}
    [CommRing K] (k : σ → ℕ) : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ k i)

theorem mem_rectangularIdeal {σ K : Type*} [CommRing K] (k : σ → ℕ)
    (p : MvPolynomial σ K) :
    p ∈ rectangularIdeal k ↔ ∀ d ∈ p.support, ∃ i, k i ≤ d i := by
  classical
  have h : Set.range (fun i => (X i : MvPolynomial σ K) ^ k i) =
      (fun d => monomial d (1 : K)) '' Set.range (fun i => Finsupp.single i (k i)) := by
    simpa only [X_pow_eq_monomial] using
      Set.range_comp' (fun d => monomial d (1 : K)) (fun i => Finsupp.single i (k i))
  simp only [rectangularIdeal, h, mem_ideal_span_monomial_image, Set.mem_range,
    exists_exists_eq_and, Finsupp.single_le_iff]

theorem rectangularIdeal_restrictScalars {σ K : Type*} [CommRing K] (k : σ → ℕ) :
    (rectangularIdeal k : Ideal (MvPolynomial σ K)).restrictScalars K =
      restrictSupport K {d | ∃ i, k i ≤ d i} := by
  ext p
  rw [Submodule.restrictScalars_mem, mem_rectangularIdeal, mem_restrictSupport_iff]
  rfl

theorem isCompl_restrictSupport_compl {σ K : Type*} [CommRing K]
    (s : Set (σ →₀ ℕ)) : IsCompl (restrictSupport K s) (restrictSupport K sᶜ) := by
  have h : IsCompl (Finsupp.supported K K s) (Finsupp.supported K K sᶜ) :=
    ⟨Finsupp.disjoint_supported_supported disjoint_compl_right,
      Finsupp.codisjoint_supported_supported (codisjoint_iff.mpr sup_compl_eq_top)⟩
  simpa only [restrictSupport, AddMonoidAlgebra.supported_eq_map] using
    Submodule.isCompl_map (AddMonoidAlgebra.coeffLinearEquiv K).symm h

def rectangularQuotientEquiv {σ K : Type*} [CommRing K] (k : σ → ℕ) :
    (MvPolynomial σ K ⧸ rectangularIdeal k) ≃ₗ[K]
      restrictSupport K {d | ∀ i, d i < k i} := by
  have h : {d : σ →₀ ℕ | ∃ i, k i ≤ d i}ᶜ = {d | ∀ i, d i < k i} := by
    ext d
    simp
  exact (Submodule.Quotient.restrictScalarsEquiv K (rectangularIdeal k)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (rectangularIdeal_restrictScalars k)).trans
      ((restrictSupport K {d | ∃ i, k i ≤ d i}).quotientEquivOfIsCompl _
        (h ▸ isCompl_restrictSupport_compl {d | ∃ i, k i ≤ d i})))

def rectangularExponentEquiv {σ : Type*} [Fintype σ] (k : σ → ℕ) :
    {d : σ →₀ ℕ // ∀ i, d i < k i} ≃ (∀ i, Fin (k i)) where
  toFun d i := ⟨d.1 i, d.2 i⟩
  invFun d := ⟨Finsupp.equivFunOnFinite.symm (fun i => (d i).val), fun i => (d i).isLt⟩
  left_inv d := by apply Subtype.ext; ext i; rfl
  right_inv d := by funext i; apply Fin.ext; rfl

def rectangularQuotientBasis {σ K : Type*} [Fintype σ] [CommRing K] (k : σ → ℕ) :
    Module.Basis (∀ i, Fin (k i)) K (MvPolynomial σ K ⧸ rectangularIdeal k) :=
  ((basisRestrictSupport K {d | ∀ i, d i < k i}).reindex
    (rectangularExponentEquiv k)).map (rectangularQuotientEquiv k).symm

theorem finrank_rectangularQuotient {σ K : Type*} [Fintype σ] [Field K] (k : σ → ℕ) :
    Module.finrank K (MvPolynomial σ K ⧸ rectangularIdeal k) = ∏ i, k i := by
  classical
  rw [Module.finrank_eq_card_basis (rectangularQuotientBasis k)]
  simp

open MvPolynomial

theorem homogeneous_mem_rectangularIdeal {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : (∑ i, (k i - 1)) < n) :
    p ∈ rectangularIdeal k := by
  classical
  apply (mem_rectangularIdeal k p).mpr
  intro d hd
  by_contra h
  push Not at h
  have hsum : (∑ i, d i) ≤ ∑ i, (k i - 1) :=
    Finset.sum_le_sum fun i _ => Nat.le_pred_of_lt (h i)
  have hdegree : n = ∑ i, d i := by
    simpa only [← Finsupp.degree_apply, Finsupp.degree_eq_sum] using
      hp.degree_eq_sum_deg_support hd
  omega

theorem rectangular_homogeneous_image_eq_bot {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) (n : ℕ) (hn : (∑ i, (k i - 1)) < n) :
    (homogeneousSubmodule σ K n).map
      (Ideal.Quotient.mkₐ K (rectangularIdeal k)).toLinearMap = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  change Ideal.Quotient.mk (rectangularIdeal k) p = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact homogeneous_mem_rectangularIdeal k
    ((mem_homogeneousSubmodule n p).mp hp) hn

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem rectangularIdeal_isHomogeneous {σ K : Type*} [CommRing K] (k : σ → ℕ) :
    (rectangularIdeal k : Ideal (MvPolynomial σ K)).IsHomogeneous
      (homogeneousSubmodule σ K) := by
  apply Ideal.homogeneous_span (homogeneousSubmodule σ K)
  rintro _ ⟨i, rfl⟩
  exact ⟨k i, isHomogeneous_X_pow i (k i)⟩

theorem quotient_finrank_le_prod_of_homogeneous_image_le_rectangular
    {L τ : Type*} [Field L] [Fintype τ]
    (I : Ideal (MvPolynomial σ K)) (k : τ → ℕ)
    (hle : ∀ n, Module.finrank K
      ((homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank L ((homogeneousSubmodule τ L n).map
        (Ideal.Quotient.mkₐ L (rectangularIdeal k)).toLinearMap)) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      Module.finrank K (MvPolynomial σ K ⧸ I) ≤ ∏ i, k i := by
  have h := quotient_finrank_le_of_homogeneous_image_finrank_le I
    (rectangularIdeal k : Ideal (MvPolynomial τ L)) (rectangularIdeal_isHomogeneous k)
    ((∑ i, (k i - 1)) + 1)
    (fun n hn => rectangular_homogeneous_image_eq_bot k n (Nat.lt_of_succ_le hn)) hle
  simpa only [finrank_rectangularQuotient] using h

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
