import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Order
import OAI.AlgebraicGeometry.PlaneCurves.BinaryForms
import OAI.AlgebraicGeometry.PlaneCurves.MatrixLimits
import OAI.AlgebraicGeometry.PlaneCurves.TaylorMultiplicity

namespace OAI

/-!
# Affine chart maps, genuine jets, and universal incidence equations
-/

section

namespace Nagata.W27

noncomputable section

open MvPolynomial

/-- The affine monomials of total degree at most `d`, indexing the usual
degree-`d` homogeneous forms after setting the third coordinate to one. -/
abbrev PlaneMonomial (d : ℕ) :=
  {ab : Fin (d + 1) × Fin (d + 1) // ab.1.val + ab.2.val ≤ d}

/-- Point and Taylor-order indices, allowing a different required order at
each point, including order zero. -/
abbrev PlaneJet (r : ℕ) (m : Fin r → ℕ) :=
  (i : Fin r) × {ab : Fin (m i) × Fin (m i) // ab.1.val + ab.2.val < m i}

section Entries

variable {R : Type*} [CommRing R]
variable {ι : Type*}

/-- The coefficient of `ξ^u η^v` in `(x+ξ)^a (y+η)^b`, written as a
polynomial in the coordinates of point `i`. This explicit expression is
used without a claimed Taylor/multiplicity bridge. -/
def affineJetEntry (i : ι) (a b u v : ℕ) : MvPolynomial (ι × Fin 2) R :=
  C ((Nat.choose a u : R) * (Nat.choose b v : R)) *
    X (i, 0) ^ (a - u) * X (i, 1) ^ (b - v)

theorem eval_affineJetEntry (p : ι × Fin 2 → R) (i : ι) (a b u v : ℕ) :
    eval p (affineJetEntry i a b u v : MvPolynomial (ι × Fin 2) R) =
      (Nat.choose a u : R) * (Nat.choose b v : R) *
        p (i, 0) ^ (a - u) * p (i, 1) ^ (b - v) := by
  simp [affineJetEntry]

theorem affineJetEntry_eq_zero_of_left (i : ι) (a b u v : ℕ) (h : a < u) :
    (affineJetEntry i a b u v : MvPolynomial (ι × Fin 2) R) = 0 := by
  simp [affineJetEntry, Nat.choose_eq_zero_of_lt h]

theorem affineJetEntry_eq_zero_of_right (i : ι) (a b u v : ℕ) (h : b < v) :
    (affineJetEntry i a b u v : MvPolynomial (ι × Fin 2) R) = 0 := by
  simp [affineJetEntry, Nat.choose_eq_zero_of_lt h]

end Entries

end

end Nagata.W27

end

section

noncomputable section

namespace Nagata.W27

open scoped BigOperators
open MvPolynomial

section MatrixEntries

variable {R : Type*} [CommRing R]

/-- The actual finite matrix of affine jet expressions. -/
def planeJetMatrix (r d : ℕ) (m : Fin r → ℕ) :
    Matrix (PlaneJet r m) (PlaneMonomial d) (MvPolynomial (Fin r × Fin 2) R) :=
  fun row col => affineJetEntry row.1 col.1.1.val col.1.2.val
    row.2.1.1.val row.2.1.2.val

end MatrixEntries

section LinearEquations

variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ]

/-- A coefficient-linear equation whose entries are polynomial in the
point coordinates. -/
def coefficientEquation (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (c : κ → R) (row : ρ) : R :=
  ∑ col, eval p (A row col) * c col

theorem coefficientEquation_add (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (c c' : κ → R) (row : ρ) :
    coefficientEquation A p (c + c') row =
      coefficientEquation A p c row + coefficientEquation A p c' row := by
  simp [coefficientEquation, mul_add, Finset.sum_add_distrib]

theorem coefficientEquation_smul (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (a : R) (c : κ → R) (row : ρ) :
    coefficientEquation A p (a • c) row = a * coefficientEquation A p c row := by
  simp only [coefficientEquation, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  exact mul_left_comm _ _ _

/-- The coefficient linear map defining the jet conditions at fixed points. -/
def coefficientLinearMap (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R) :
    (κ → R) →ₗ[R] (ρ → R) where
  toFun c row := coefficientEquation A p c row
  map_add' c c' := funext (coefficientEquation_add A p c c')
  map_smul' a c := funext (coefficientEquation_smul A p a c)

/-- The affine incidence equation, now polynomial jointly in point coordinates
and form coefficients. -/
def incidenceEquation (A : Matrix ρ κ (MvPolynomial σ R)) (row : ρ) :
    MvPolynomial (σ ⊕ κ) R :=
  ∑ col, eval₂ C (fun s => X (Sum.inl s)) (A row col) * X (Sum.inr col)

theorem eval_incidenceEquation (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (c : κ → R) (row : ρ) :
    eval (Sum.elim p c) (incidenceEquation A row) = coefficientEquation A p c row := by
  simp only [incidenceEquation, map_sum, map_mul, eval_X, Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro col _
  congr 1
  rw [← eval_assoc]
  simp only [Function.comp_def, eval_X, Sum.elim_inl]

/-- Common zero set of a family of actual polynomials. No topological or
geometric consequence is built into this definition. -/
def polynomialZeroSet {τ : Type*} (f : τ → MvPolynomial σ R) : Set (σ → R) :=
  {p | ∀ t, eval p (f t) = 0}

theorem incidence_zeroSet_iff (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (c : κ → R) :
    Sum.elim p c ∈ polynomialZeroSet (incidenceEquation A) ↔
      coefficientLinearMap A p c = 0 := by
  change (∀ row, eval (Sum.elim p c) (incidenceEquation A row) = 0) ↔ _
  simp only [eval_incidenceEquation]
  change (∀ row, coefficientEquation A p c row = 0) ↔
    (fun row => coefficientEquation A p c row) = (fun _ => 0)
  exact Iff.symm funext_iff

end LinearEquations

end Nagata.W27

end
end

section

noncomputable section

namespace Nagata.W27

open MvPolynomial

attribute [local instance] Classical.decEq

/-- All global ternary monomials of degree exactly `d`; these columns are
independent of the affine charts chosen at the marked points. -/
abbrev HomogeneousMonomial (d : ℕ) := Nagata.W02.DegreeExponent d

variable {R : Type*} [CommRing R]

/-- A genuine coefficient linear equivalence for the full space of
degree-`d` homogeneous ternary forms. -/
def homogeneousCoordinates (d : ℕ) :
    homogeneousSubmodule (Fin 3) R d ≃ₗ[R] (HomogeneousMonomial d → R) :=
  (Nagata.W02.homogeneousCoefficientEquiv R d).trans
    (Finsupp.linearEquivFunOnFinite R R (HomogeneousMonomial d))

@[simp] theorem homogeneousCoordinates_apply (d : ℕ)
    (F : homogeneousSubmodule (Fin 3) R d) (a : HomogeneousMonomial d) :
    homogeneousCoordinates d F a = F.val.coeff a.val := rfl

@[simp] theorem homogeneousCoordinates_symm_coeff (d : ℕ)
    (c : HomogeneousMonomial d → R) (a : HomogeneousMonomial d) :
    ((homogeneousCoordinates d).symm c).val.coeff a.val = c a := by
  exact congrFun ((homogeneousCoordinates d).apply_symm_apply c) a

@[simp] theorem homogeneousCoordinates_symm_single (d : ℕ)
    (a : HomogeneousMonomial d) (z : R) :
    ((homogeneousCoordinates d).symm (Pi.single a z)).val = monomial a.val z := by
  simp [homogeneousCoordinates, Finsupp.linearEquivFunOnFinite_symm_single]

theorem homogeneousCoordinates_ne_zero_iff (d : ℕ)
    (F : homogeneousSubmodule (Fin 3) R d) :
    homogeneousCoordinates d F ≠ 0 ↔ F.val ≠ 0 := by
  constructor
  · intro h hz
    apply h
    have hF : F = 0 := Subtype.ext hz
    rw [hF, map_zero]
  · intro h hz
    apply h
    have hF : F = 0 := (homogeneousCoordinates d).injective
      (hz.trans (map_zero (homogeneousCoordinates d)).symm)
    exact congrArg Subtype.val hF

theorem homogeneousCoordinates_symm_ne_zero_iff (d : ℕ)
    (c : HomogeneousMonomial d → R) :
    ((homogeneousCoordinates d).symm c).val ≠ 0 ↔ c ≠ 0 := by
  rw [← homogeneousCoordinates_ne_zero_iff]
  rw [LinearEquiv.apply_symm_apply]

end Nagata.W27

end
end

section

noncomputable section

namespace Nagata.W27

open MvPolynomial

variable {ι R : Type*} [CommRing R]

/-- Translation with indeterminate point coordinates. The coefficients are
actual polynomials in the point variables. -/
def universalTranslate (i : ι) :
    MvPolynomial (Fin 2) R →+*
      MvPolynomial (Fin 2) (MvPolynomial (ι × Fin 2) R) :=
  eval₂Hom (C.comp C) (fun j => X j + C (X (i, j)))

/-- An actual Taylor coefficient polynomial, without a binomial-formula
assumption. -/
def universalJetCoefficient (i : ι) (s : Fin 2 →₀ ℕ)
    (f : MvPolynomial (Fin 2) R) : MvPolynomial (ι × Fin 2) R :=
  (universalTranslate i f).coeff s

theorem map_universalTranslate (p : ι × Fin 2 → R) (i : ι)
    (f : MvPolynomial (Fin 2) R) :
    MvPolynomial.map (eval p) (universalTranslate i f) =
      eval₂Hom C (fun j => X j + C (p (i, j))) f := by
  have h : (MvPolynomial.map (eval p)).comp (universalTranslate i) =
      eval₂Hom C (fun j => X j + C (p (i, j))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [universalTranslate]
    · intro j
      simp [universalTranslate]
  exact RingHom.congr_fun h f

/-- Specializing the polynomial point parameters gives the genuine finite
Taylor coefficient of the translated polynomial. -/
theorem eval_universalJetCoefficient (p : ι × Fin 2 → R) (i : ι)
    (s : Fin 2 →₀ ℕ) (f : MvPolynomial (Fin 2) R) :
    eval p (universalJetCoefficient i s f) =
      (eval₂Hom C (fun j => X j + C (p (i, j))) f).coeff s := by
  rw [universalJetCoefficient, ← coeff_map, map_universalTranslate]

theorem universalJetCoefficient_add (i : ι) (s : Fin 2 →₀ ℕ)
    (f g : MvPolynomial (Fin 2) R) :
    universalJetCoefficient i s (f + g) =
      universalJetCoefficient i s f + universalJetCoefficient i s g := by
  simp [universalJetCoefficient]

theorem universalJetCoefficient_C_mul (i : ι) (s : Fin 2 →₀ ℕ)
    (a : R) (f : MvPolynomial (Fin 2) R) :
    universalJetCoefficient i s (C a * f) =
      C a * universalJetCoefficient i s f := by
  simp [universalJetCoefficient, universalTranslate, coeff_C_mul]

end Nagata.W27

end
end

section

/-!
# Polynomial equations for affine plane jets
-/

namespace Nagata.W27

noncomputable section

open scoped BigOperators
open MvPolynomial

section Determinants

variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ] [DecidableEq κ]

/-- Full-column-size minor polynomial, with rows selected by `s`.
Repeated row selections cause no problem and require no artificial
ordering of the finite column set. -/
def minorPolynomial (A : Matrix ρ κ (MvPolynomial σ R)) (s : κ → ρ) :
    MvPolynomial σ R :=
  Matrix.det (fun i j => A (s i) j)

theorem eval_minorPolynomial (A : Matrix ρ κ (MvPolynomial σ R))
    (s : κ → ρ) (p : σ → R) :
    eval p (minorPolynomial A s) = Matrix.det (fun i j => eval p (A (s i) j)) := by
  exact (eval p).map_det _

theorem minor_zeroSet_iff (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R) :
    p ∈ polynomialZeroSet (minorPolynomial A) ↔
      ∀ s : κ → ρ, Matrix.det (fun i j => eval p (A (s i) j)) = 0 := by
  simp only [polynomialZeroSet, Set.mem_ofPred_eq, eval_minorPolynomial]

theorem minor_eq_zero_of_nonzero_kernel [IsDomain R]
    (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R)
    (c : κ → R) (hc : coefficientLinearMap A p c = 0) (hcne : c ≠ 0)
    (s : κ → ρ) : eval p (minorPolynomial A s) = 0 := by
  rw [eval_minorPolynomial]
  apply Matrix.det_eq_zero_of_not_linearIndependent_cols
  intro hli
  have hz : (∑ col, c col • (fun i => eval p (A (s i) col))) = 0 := by
    funext i
    have hrow : coefficientEquation A p c (s i) = 0 := congrFun hc (s i)
    simpa only [coefficientEquation, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_comm] using hrow
  have hc0 : ∀ col, c col = 0 := Fintype.linearIndependent_iff.mp hli c hz
  exact hcne (funext hc0)

theorem mem_minor_zeroSet_of_nonzero_kernel [IsDomain R]
    (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R)
    (c : κ → R) (hc : coefficientLinearMap A p c = 0) (hcne : c ≠ 0) :
    p ∈ polynomialZeroSet (minorPolynomial A) :=
  fun s => minor_eq_zero_of_nonzero_kernel A p c hc hcne s

end Determinants

end

end Nagata.W27

end

section

noncomputable section

namespace Nagata.W27

open MvPolynomial

/-- Affine Zariski topology: the topology generated by principal open sets
on which a multivariate polynomial does not vanish. -/
@[reducible] def affineZariski (σ R : Type*) [CommRing R] : TopologicalSpace (σ → R) :=
  TopologicalSpace.generateFrom
    (Set.range fun f : MvPolynomial σ R => {p : σ → R | eval p f ≠ 0})

theorem isClosed_polynomialEquation {σ R : Type*} [CommRing R]
    (f : MvPolynomial σ R) :
    @IsClosed (σ → R) (affineZariski σ R) {p : σ → R | eval p f = 0} := by
  let := affineZariski σ R
  apply isOpen_compl_iff.mp
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨f, rfl⟩

theorem isClosed_polynomialZeroSet {σ R τ : Type*} [CommRing R]
    (f : τ → MvPolynomial σ R) :
    @IsClosed (σ → R) (affineZariski σ R) (polynomialZeroSet f) := by
  let := affineZariski σ R
  have hz : polynomialZeroSet f = ⋂ t, {p : σ → R | eval p (f t) = 0} := by
    ext p
    simp only [polynomialZeroSet, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hz]
  exact isClosed_iInter fun t => isClosed_polynomialEquation (f t)

/-- The coefficient-linear incidence equations form a Zariski-closed
subset of the joint affine point/coefficient space. This includes the zero
coefficient vector; projectivization of coefficients remains separate. -/
theorem isClosed_affineIncidence {σ R κ ρ : Type*} [CommRing R] [Fintype κ]
    (A : Matrix ρ κ (MvPolynomial σ R)) :
    @IsClosed ((σ ⊕ κ) → R) (affineZariski (σ ⊕ κ) R)
      (polynomialZeroSet (incidenceEquation A)) :=
  isClosed_polynomialZeroSet _

end Nagata.W27

end
end

section

noncomputable section

namespace Nagata.W27

open scoped BigOperators
open MvPolynomial

variable {R σ : Type*} [CommRing R]

theorem shifted_power_expansion (i : σ) (x : R) (a : ℕ) :
    (X i + C x : MvPolynomial σ R) ^ a =
      ∑ k ∈ Finset.range (a + 1),
        monomial (Finsupp.single i k) (x ^ (a - k) * (Nat.choose a k : R)) := by
  classical
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp [monomial_eq, mul_left_comm, mul_comm]

/-- The two-variable translated monomial has exactly the displayed binomial
Taylor coefficient, including Taylor exponents outside its support. -/
theorem coeff_shifted_monomial (x y : R) (a b u v : ℕ) :
    ((X (0 : Fin 2) + C x) ^ a * (X (1 : Fin 2) + C y) ^ b).coeff
        (Nagata.Workers.W30.exponentPair u v) =
      (Nat.choose a u : R) * (Nat.choose b v : R) *
        x ^ (a - u) * y ^ (b - v) := by
  classical
  rw [shifted_power_expansion, shifted_power_expansion, Finset.sum_mul]
  simp only [Finset.mul_sum, coeff_sum, monomial_mul_monomial]
  have hpair : ∀ i j, Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j =
      Nagata.Workers.W30.exponentPair u v ↔ i = u ∧ j = v := by
    intro i j
    change Nagata.Workers.W30.exponentPair i j =
      Nagata.Workers.W30.exponentPair u v ↔ _
    constructor
    · intro h
      exact Prod.mk.inj (Nagata.Workers.W30.exponentPair_injective h)
    · rintro ⟨rfl, rfl⟩
      rfl
  by_cases hu : u < a + 1
  · by_cases hv : v < b + 1
    · simp [coeff_monomial, hpair, ite_and, hu, hv, mul_assoc, mul_left_comm, mul_comm]
    · have hb : b < v := by omega
      simp [coeff_monomial, hpair, ite_and, hv, Nat.choose_eq_zero_of_lt hb]
  · have ha : a < u := by omega
    simp [coeff_monomial, hpair, ite_and, hu, Nat.choose_eq_zero_of_lt ha]

/-- The initially displayed binomial matrix entries are exactly the genuine
universal Taylor-coefficient polynomials, as a polynomial identity over any
commutative coefficient ring. -/
theorem universalJetCoefficient_monomial {ι : Type*} (i : ι) (a b u v : ℕ) :
    universalJetCoefficient i (Nagata.Workers.W30.exponentPair u v)
      ((X (0 : Fin 2)) ^ a * (X 1) ^ b : MvPolynomial (Fin 2) R) =
      affineJetEntry i a b u v := by
  simp only [universalJetCoefficient, universalTranslate, map_mul, map_pow, eval₂Hom_X']
  rw [coeff_shifted_monomial]
  simp [affineJetEntry]

end Nagata.W27

end
end

section

noncomputable section

namespace Nagata.W27

open scoped BigOperators
open MvPolynomial

variable {R : Type*} [CommRing R]

/-- Actual dehomogenization in chart `c`, with the two surviving coordinates
ordered by `Fin.succAbove`. -/
def directChartHom (c : Fin 3) : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 2) R :=
  eval₂Hom C (Fin.insertNth (α := fun _ : Fin 3 => MvPolynomial (Fin 2) R) c 1 X)

def directChartLinearMap (c : Fin 3) :
    MvPolynomial (Fin 3) R →ₗ[R] MvPolynomial (Fin 2) R where
  toFun := directChartHom c
  map_add' := (directChartHom c).map_add
  map_smul' a f := by simp [smul_eq_C_mul, directChartHom]

def universalJetLinearMap {ι : Type*} (i : ι) (s : Fin 2 →₀ ℕ) :
    MvPolynomial (Fin 2) R →ₗ[R] MvPolynomial (ι × Fin 2) R where
  toFun := universalJetCoefficient i s
  map_add' := universalJetCoefficient_add i s
  map_smul' a f := by
    simp only [smul_eq_C_mul, universalJetCoefficient_C_mul, RingHom.id_apply]

theorem linearMap_eq_sum_basis {κ M : Type*} [Fintype κ] [DecidableEq κ]
    [AddCommMonoid M] [Module R M] (L : (κ → R) →ₗ[R] M) (x : κ → R) :
    L x = ∑ j, x j • L (Pi.single j 1) := by
  classical
  have hx : x = ∑ j, x j • (Pi.single j (1 : R) : κ → R) := by
    funext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul]

end Nagata.W27

end
end

section

/-!
# Affine Zariski closedness of the jet equations

The topology is the genuine affine Zariski topology defined by principal
polynomial nonvanishing opens. Its comparison with the product-projective
configuration space is a separate chart theorem.
-/

namespace Nagata.W27

noncomputable section

open MvPolynomial

/-- Vanishing of all full-column-size minors is a Zariski-closed
condition on the affine point coordinates. -/
theorem isClosed_minorZeroSet {σ R κ ρ : Type*} [CommRing R]
    [Fintype κ] [DecidableEq κ] (A : Matrix ρ κ (MvPolynomial σ R)) :
    @IsClosed (σ → R) (affineZariski σ R) (polynomialZeroSet (minorPolynomial A)) :=
  isClosed_polynomialZeroSet _

end

end Nagata.W27

end

section

noncomputable section

namespace Nagata.W27

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- Dehomogenization of an actual global ternary monomial in any chart.
Its two exponents are read from the same global exponent vector. -/
theorem directChartHom_monomial (c : Fin 3) (a : Fin 3 →₀ ℕ) (z : R) :
    directChartHom c (monomial a z) =
      C z * (X (0 : Fin 2)) ^ a (c.succAbove 0) * (X 1) ^ a (c.succAbove 1) := by
  rw [directChartHom, eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succAbove _ c]
  simp [Fin.prod_univ_two, mul_assoc]

/-- In every point chart, the genuine Taylor coefficient of a global
monomial is the claimed binomial polynomial in that chart's coordinates. -/
theorem universalJetCoefficient_chart_monomial {ι : Type*}
    (i : ι) (c : Fin 3) (a : Fin 3 →₀ ℕ) (u v : ℕ) :
    universalJetCoefficient i (Nagata.Workers.W30.exponentPair u v)
      (directChartHom c (monomial a (1 : R))) =
        affineJetEntry i (a (c.succAbove 0)) (a (c.succAbove 1)) u v := by
  rw [directChartHom_monomial]
  simp only [map_one, one_mul]
  exact universalJetCoefficient_monomial i _ _ u v

end Nagata.W27

end
end

section

noncomputable section

namespace Nagata.W27

open MvPolynomial

variable {σ ρ κ K : Type*} [Field K]
variable [Fintype ρ] [Fintype κ] [DecidableEq κ]

/-- The full rectangular determinantal criterion. No cardinal restriction,
positive multiplicity, or nonempty-row hypothesis is imposed. -/
theorem nonzero_kernel_iff_minor_zeroSet
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → K) :
    (∃ c : κ → K, c ≠ 0 ∧ coefficientLinearMap A p c = 0) ↔
      p ∈ polynomialZeroSet (minorPolynomial A) := by
  constructor
  · rintro ⟨c, hc, hAc⟩
    exact mem_minor_zeroSet_of_nonzero_kernel A p c hAc hc
  · intro h
    obtain ⟨c, hc, hAc⟩ :=
      Nagata.Workers.W11.exists_nonzero_kernel_coordinates_of_all_maximal_minors_zero
        (fun i j => eval p (A i j)) ((minor_zeroSet_iff A p).mp h)
    exact ⟨c, hc, funext hAc⟩

/-- Existence of a nonzero coefficient vector solving a polynomial linear
system is an affine Zariski-closed condition on its parameters. -/
theorem isClosed_nonzero_kernel_locus
    (A : Matrix ρ κ (MvPolynomial σ K)) :
    @IsClosed (σ → K) (affineZariski σ K)
      {p | ∃ c : κ → K, c ≠ 0 ∧ coefficientLinearMap A p c = 0} := by
  have heq : {p | ∃ c : κ → K, c ≠ 0 ∧ coefficientLinearMap A p c = 0} =
      polynomialZeroSet (minorPolynomial A) := by
    ext p
    exact nonzero_kernel_iff_minor_zeroSet A p
  rw [heq]
  exact isClosed_minorZeroSet A

end Nagata.W27

end
end

section

noncomputable section

namespace Nagata.W27

open MvPolynomial

variable {r : ℕ} {R : Type*} [CommRing R]

/-- The actual two-variable exponent selected by a finite plane jet row. -/
def planeJetExponent {m : Fin r → ℕ} (row : PlaneJet r m) : Fin 2 →₀ ℕ :=
  Nagata.Workers.W30.exponentPair row.2.val.1.val row.2.val.2.val

/-- Finite jet rows exactly express ordinary evaluation-ideal multiplicity
at every point. Different affine polynomials at different chart locations
are allowed here; the projective application uses charts of one global form. -/
theorem all_orders_iff_universal_jets (p : Fin r × Fin 2 → R)
    (m : Fin r → ℕ) (f : Fin r → MvPolynomial (Fin 2) R) :
    (∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i) (f i)) ↔
      ∀ row : PlaneJet r m,
        eval p (universalJetCoefficient row.1 (planeJetExponent row) (f row.1)) = 0 := by
  constructor
  · intro h row
    rw [eval_universalJetCoefficient]
    exact (Nagata.AffineMultiplicity.orderAtLeast_finTwo_iff_taylor_coeff
      _ _ _).mp (h row.1) row.2.val.1.val row.2.val.2.val row.2.property
  · intro h i
    apply (Nagata.AffineMultiplicity.orderAtLeast_finTwo_iff_taylor_coeff _ _ _).mpr
    intro u v huv
    have hu : u < m i := by omega
    have hv : v < m i := by omega
    let row : PlaneJet r m := ⟨i, ⟨(⟨u, hu⟩, ⟨v, hv⟩), huv⟩⟩
    have hr := h row
    rw [eval_universalJetCoefficient] at hr
    exact hr

end Nagata.W27

end
end

section

noncomputable section

namespace Nagata.W27

open scoped BigOperators
open MvPolynomial

attribute [local instance] Classical.decEq

variable {R : Type*} [CommRing R]

variable {r : ℕ}

/-- Polynomial jet of one actual global homogeneous form at one point chart. -/
def chartJetPolynomialMap (c : Fin r → Fin 3) (d : ℕ) (m : Fin r → ℕ)
    (row : PlaneJet r m) :
    homogeneousSubmodule (Fin 3) R d →ₗ[R] MvPolynomial (Fin r × Fin 2) R :=
  (universalJetLinearMap row.1 (planeJetExponent row)).comp
    ((directChartLinearMap (c row.1)).comp (homogeneousSubmodule (Fin 3) R d).subtype)

/-- The matrix uses a single basis of the global homogeneous form space,
regardless of which affine chart is selected at each individual point. -/
def chartPlaneJetMatrix (c : Fin r → Fin 3) (d : ℕ) (m : Fin r → ℕ) :
    Matrix (PlaneJet r m) (HomogeneousMonomial d) (MvPolynomial (Fin r × Fin 2) R) :=
  fun row col => chartJetPolynomialMap c d m row
    ((homogeneousCoordinates d).symm (Pi.single col 1))

/-- The matrix's global-basis columns have exactly the expected binomial
entries in each individual affine chart. -/
theorem chartPlaneJetMatrix_entry (c : Fin r → Fin 3) (d : ℕ)
    (m : Fin r → ℕ) (row : PlaneJet r m) (col : HomogeneousMonomial d) :
    chartPlaneJetMatrix (R := R) c d m row col =
      affineJetEntry row.1 (col.val ((c row.1).succAbove 0))
        (col.val ((c row.1).succAbove 1)) row.2.val.1.val row.2.val.2.val := by
  change universalJetCoefficient row.1 (planeJetExponent row)
    (directChartHom (c row.1) ((homogeneousCoordinates d).symm (Pi.single col 1)).val) = _
  rw [homogeneousCoordinates_symm_single]
  exact universalJetCoefficient_chart_monomial row.1 (c row.1) col.val _ _

/-- Specialization of the actual global-basis matrix is exactly the ordinary
Taylor jet of the actual dehomogenized homogeneous polynomial. -/
theorem coefficientEquation_chartPlaneJetMatrix (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R)
    (F : homogeneousSubmodule (Fin 3) R d) (row : PlaneJet r m) :
    coefficientEquation (chartPlaneJetMatrix c d m) p (homogeneousCoordinates d F) row =
      eval p (universalJetCoefficient row.1 (planeJetExponent row)
        (directChartHom (c row.1) F.val)) := by
  classical
  have h := linearMap_eq_sum_basis
    ((chartJetPolynomialMap c d m row).comp (homogeneousCoordinates d).symm.toLinearMap)
    (homogeneousCoordinates d F)
  have he := congrArg (eval p) h
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, map_sum, smul_eval,
    chartPlaneJetMatrix, chartJetPolynomialMap, universalJetLinearMap,
    directChartLinearMap, Submodule.coe_subtype, LinearMap.coe_mk,
    AddHom.coe_mk, coefficientEquation, mul_comm] using he.symm

/-- Genuine geometric order conditions in any chosen point charts are exactly
the kernel equations of the actual polynomial matrix. -/
theorem chart_orders_iff_kernel (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R)
    (F : homogeneousSubmodule (Fin 3) R d) :
    (∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i)
      (directChartHom (c i) F.val)) ↔
      coefficientLinearMap (chartPlaneJetMatrix c d m) p (homogeneousCoordinates d F) = 0 := by
  rw [all_orders_iff_universal_jets]
  change (∀ row, _) ↔ (fun row => coefficientEquation _ _ _ row) = (fun _ => 0)
  rw [funext_iff]
  exact forall_congr' fun row => by rw [coefficientEquation_chartPlaneJetMatrix]

/-- Both directions retain nonzero actual forms; no curve existence is hidden
in the coordinate-space construction. -/
theorem exists_nonzero_form_iff_chart_kernel (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R) :
    (∃ F : homogeneousSubmodule (Fin 3) R d, F.val ≠ 0 ∧
      ∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i)
        (directChartHom (c i) F.val)) ↔
      ∃ v : HomogeneousMonomial d → R, v ≠ 0 ∧
        coefficientLinearMap (chartPlaneJetMatrix c d m) p v = 0 := by
  constructor
  · rintro ⟨F, hF, horder⟩
    exact ⟨homogeneousCoordinates d F,
      (homogeneousCoordinates_ne_zero_iff d F).mpr hF,
      (chart_orders_iff_kernel c d m p F).mp horder⟩
  · rintro ⟨v, hv, hker⟩
    refine ⟨(homogeneousCoordinates d).symm v,
      (homogeneousCoordinates_symm_ne_zero_iff d v).mpr hv, ?_⟩
    apply (chart_orders_iff_kernel c d m p _).mpr
    simpa only [LinearEquiv.apply_symm_apply] using hker

end Nagata.W27

end
end

section

noncomputable section

namespace Nagata.W27

open MvPolynomial

attribute [local instance] Classical.decEq

variable {r : ℕ} {K : Type*} [Field K]

/-- On each product chart, existence of an actual nonzero homogeneous form
with arbitrary assigned ordinary multiplicities is precisely a common
zero set of actual polynomial minors. -/
theorem exists_nonzero_form_iff_chart_minors (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → K) :
    (∃ F : homogeneousSubmodule (Fin 3) K d, F.val ≠ 0 ∧
      ∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i)
        (directChartHom (c i) F.val)) ↔
      p ∈ polynomialZeroSet (minorPolynomial (chartPlaneJetMatrix c d m)) := by
  classical
  exact (exists_nonzero_form_iff_chart_kernel c d m p).trans
    (nonzero_kernel_iff_minor_zeroSet (chartPlaneJetMatrix c d m) p)

theorem isClosed_chart_form_locus (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) :
    @IsClosed (Fin r × Fin 2 → K) (affineZariski (Fin r × Fin 2) K)
      {p | ∃ F : homogeneousSubmodule (Fin 3) K d, F.val ≠ 0 ∧
        ∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i)
          (directChartHom (c i) F.val)} := by
  classical
  have heq : {p | ∃ F : homogeneousSubmodule (Fin 3) K d, F.val ≠ 0 ∧
        ∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i)
          (directChartHom (c i) F.val)} =
      polynomialZeroSet (minorPolynomial (chartPlaneJetMatrix c d m)) := by
    ext p
    exact exists_nonzero_form_iff_chart_minors c d m p
  rw [heq]
  exact isClosed_minorZeroSet _

end Nagata.W27

end
end

end OAI
