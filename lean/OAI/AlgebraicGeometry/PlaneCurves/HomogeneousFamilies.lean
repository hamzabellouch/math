import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import OAI.AlgebraicGeometry.PlaneCurves.ChartJets
import OAI.AlgebraicGeometry.PlaneCurves.DividedFamilies
import OAI.AlgebraicGeometry.PlaneCurves.NormalCoefficients

namespace OAI

/-!
# Polynomial families, homogeneous lifts, and parameter transposition; Factored homogeneous families in affine charts
-/

section

/-!
# Homogeneous lifts in normal specialization

A degree-d family is a genuine polynomial in the parameter whose coefficients
are homogeneous plane polynomials of degree d. Quotients by powers of a
homogeneous equation retain exactly the required homogeneous degree.
No global section or multiplicity conclusion is stored in these definitions.
-/

namespace Nagata.Workers.W17

variable {K σ : Type*} [CommRing K] [IsDomain K]

/-- Genuine one-parameter families of homogeneous plane forms. -/
def HomogeneousPlaneFamily (K : Type*) [CommRing K] (d : Nat) :=
  {S : Polynomial (MvPolynomial (Fin 3) K) //
    ∀ α, (S.coeff α).IsHomogeneous d}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Dividing a nonzero homogeneous polynomial by a homogeneous factor
produces a homogeneous quotient of the degree difference. -/
theorem homogeneous_factor_degree {P Q : MvPolynomial σ K} {k d : Nat}
    (hP : P.IsHomogeneous k) (hPQ : (P * Q).IsHomogeneous d)
    (hne : P * Q ≠ 0) :
    k ≤ d ∧ Q.IsHomogeneous (d - k) := by
  let H := MvPolynomial.homogeneousSubmodule σ K
  have hsame : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) = P * Q :=
    DirectSum.decompose_of_mem_same H hPQ
  have hkd : k ≤ d := by
    by_contra hk
    have hzero : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) = 0 :=
      DirectSum.coe_decompose_mul_of_left_mem_of_not_le H hP hk
    exact hne (hsame.symm.trans hzero)
  have hpart : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) =
      P * (DirectSum.decompose H Q (d - k) : MvPolynomial σ K) :=
    DirectSum.coe_decompose_mul_of_left_mem_of_le H hP hkd
  have hQ : Q = (DirectSum.decompose H Q (d - k) : MvPolynomial σ K) :=
    mul_left_cancel₀ (left_ne_zero_of_mul hne) (hsame.symm.trans hpart)
  refine ⟨hkd, ?_⟩
  change Q ∈ H (d - k)
  rw [hQ]
  exact (DirectSum.decompose H Q (d - k)).property

/-- The remainder lift in S=G^j*T has degree d-kj and kj≤d. -/
theorem homogeneous_power_remainder {S G T : MvPolynomial σ K} {d k j : Nat}
    (hS : S.IsHomogeneous d) (hG : G.IsHomogeneous k)
    (hne : S ≠ 0) (hfactor : S = G ^ j * T) :
    k * j ≤ d ∧ T.IsHomogeneous (d - k * j) := by
  apply homogeneous_factor_degree (hG.pow j)
  · rwa [← hfactor]
  · rwa [← hfactor]

/-- The normal exponent is bounded by floor(d/k), with k positive. -/
theorem homogeneous_power_exponent_bound {S G T : MvPolynomial σ K} {d k j : Nat}
    (hS : S.IsHomogeneous d) (hG : G.IsHomogeneous k)
    (hne : S ≠ 0) (hfactor : S = G ^ j * T) (hk : 0 < k) :
    j ≤ d / k := by
  apply (Nat.le_div_iff_mul_le hk).mpr
  simpa [Nat.mul_comm] using (homogeneous_power_remainder hS hG hne hfactor).1

end Nagata.Workers.W17

end

section

namespace Nagata.Workers.W17

/-- Positive-degree homogeneous equations are nonunits in the genuine
polynomial ring, including the zero equation. -/
theorem positive_homogeneous_not_isUnit {K σ : Type*} [CommRing K] [Nontrivial K]
    {G : MvPolynomial σ K} {k : ℕ} (hG : G.IsHomogeneous k) (hk : 0 < k) :
    ¬IsUnit G := by
  have hzero : MvPolynomial.eval (0 : σ → K) G = 0 := by
    rw [MvPolynomial.eval_zero]
    exact hG.coeff_eq_zero (by simpa using Nat.ne_of_lt hk)
  intro hu
  have hi := hu.map (MvPolynomial.eval (0 : σ → K))
  rw [hzero] at hi
  exact not_isUnit_zero hi

end Nagata.Workers.W17

end

section

/-!
# Lowest normal polynomial of a genuine finite polynomial family

The family is an element of A[s], not an abstract object carrying its own
conclusion. Maximal powers of G are extracted using well-founded divisibility.
The resulting polynomial lies in (A/(G))[w].
-/

namespace Nagata.Workers.W17

open scoped BigOperators

variable {A : Type*} [CommRing A] [WfDvdMonoid A]

/-- Extract maximal G-powers from all nonzero coefficients of an actual
polynomial. Values at zero coefficients are normalized to exponent zero. -/
theorem exists_factored_coefficients (S : Polynomial A) (G : A)
    (hG : ¬IsUnit G) :
    ∃ (j : Nat → Nat) (T : Nat → A),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α, S.coeff α ≠ 0 → ¬G ∣ T α) := by
  classical
  have hfactor : ∀ α : Nat, ∃ n : Nat, ∃ t : A,
      S.coeff α = G ^ n * t ∧ (S.coeff α ≠ 0 → ¬G ∣ t) := by
    intro α
    by_cases hα : S.coeff α = 0
    · exact ⟨0, 0, by simp [hα], fun hn => (hn hα).elim⟩
    · obtain ⟨n, t, hnot, heq⟩ := WfDvdMonoid.max_power_factor' hα hG
      exact ⟨n, t, heq, fun _ => hnot⟩
  choose j T hfac hnot using hfactor
  exact ⟨j, T, hfac, hnot⟩

/-- A nonzero family has a nonzero lowest normal polynomial after reduction
modulo G. All factorization and minimum-weight data are constructed here. -/
theorem exists_nonzero_normal_initial
    (S : Polynomial A) (G : A) (hS : S ≠ 0) (hG : ¬IsUnit G) :
    ∃ (j : Nat → Nat) (T : Nat → A) (u : Nat),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α ∈ S.support, ¬G ∣ T α) ∧
      (∀ α ∈ S.support, u ≤ α + j α) ∧
      (S.support.filter (fun α => α + j α = u)).Nonempty ∧
      (∑ α ∈ S.support.filter (fun α => α + j α = u),
        Polynomial.monomial (j α)
          (Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α))) ≠ 0 := by
  classical
  obtain ⟨j, T, hfactor, hnot⟩ := exists_factored_coefficients S G hG
  have hnonzero : ∀ α ∈ S.support,
      Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α) ≠ 0 := by
    intro α hα hz
    exact hnot α (Polynomial.mem_support_iff.mp hα)
      ((Ideal.Quotient.eq_zero_iff_dvd G (T α)).mp hz)
  obtain ⟨u, hmin, hselected, hinitial⟩ :=
    Nagata.W18.exists_lowest_weight_polynomial S.support j
      (fun α => Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α))
      (Polynomial.support_nonempty.mpr hS) hnonzero
  exact ⟨j, T, u, hfactor, fun α hα => hnot α (Polynomial.mem_support_iff.mp hα),
    hmin, hselected, hinitial⟩

omit [WfDvdMonoid A] in
/-- Normalization S(0)≠0 bounds the selected weight by the extracted
G-exponent of the zeroth coefficient. -/
theorem initial_weight_bound_from_constant (S : Polynomial A)
    (j : Nat → Nat) (u : Nat) (hzero : S.coeff 0 ≠ 0)
    (hmin : ∀ α ∈ S.support, u ≤ α + j α) : u ≤ j 0 := by
  simpa using hmin 0 (Polynomial.mem_support_iff.mpr hzero)

end Nagata.Workers.W17

end

section

/-!
# Actual polynomial lifts indexed by normal degree

The source initially labels selected coefficients by the parameter exponent α.
Here we retain all actual lifts in one polynomial F(w) over the ambient ring;
its coefficient at normal degree n is the finite sum of the selected lifts
having jα=n. Mapping coefficients to A/(G) recovers the checked nonzero normal
polynomial. This is suitable for literal line restriction and evaluation maps.
-/

namespace Nagata.Workers.W17

open scoped BigOperators
variable {A : Type*} [CommRing A]

noncomputable def liftedNormalPolynomial
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) : Polynomial A :=
  ∑ α ∈ indices, Polynomial.monomial (j α) (T α)

/-- Grouping by normal exponent retains actual coefficient-ring elements. -/
theorem coeff_liftedNormalPolynomial
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (n : Nat) :
    (liftedNormalPolynomial indices j T).coeff n =
      ∑ α ∈ indices.filter (fun α => j α = n), T α := by
  classical
  simp only [liftedNormalPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finset.sum_filter]

/-- Mapping the actual lifted polynomial gives the literal quotient sum. -/
theorem map_liftedNormalPolynomial {B : Type*} [CommRing B]
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (f : A →+* B) :
    (liftedNormalPolynomial indices j T).map f =
      ∑ α ∈ indices, Polynomial.monomial (j α) (f (T α)) := by
  simp only [liftedNormalPolynomial, Polynomial.map_sum, Polynomial.map_monomial]

/-- The quotient of the lifted polynomial is nonzero; no global section
or reduction-to-lines property is assumed. -/
theorem quotient_liftedNormalPolynomial_ne_zero
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (G : A) (u : Nat)
    (hne : indices.Nonempty) (hweight : ∀ α ∈ indices, α + j α = u)
    (hnot : ∀ α ∈ indices, ¬G ∣ T α) :
    (liftedNormalPolynomial indices j T).map
      (Ideal.Quotient.mk (Ideal.span ({G} : Set A))) ≠ 0 := by
  rw [map_liftedNormalPolynomial]
  exact Nagata.W18.principal_diagonal_polynomial_ne_zero
    indices G T j u hne hweight hnot

/-- A bound for selected exponents is a bound for every nonzero coefficient. -/
theorem coeff_liftedNormalPolynomial_eq_zero_above
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (bound n : Nat)
    (hbound : ∀ α ∈ indices, j α ≤ bound) (hn : bound < n) :
    (liftedNormalPolynomial indices j T).coeff n = 0 := by
  classical
  have hempty : indices.filter (fun α => j α = n) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro α hα heq
    have hle : n ≤ bound := heq ▸ hbound α hα
    exact (Nat.not_lt_of_ge hle) hn
  rw [coeff_liftedNormalPolynomial, hempty, Finset.sum_empty]

/-- The genuine lifted polynomial has bounded normal-variable degree. -/
theorem natDegree_liftedNormalPolynomial_le
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (bound : Nat)
    (hbound : ∀ α ∈ indices, j α ≤ bound) :
    (liftedNormalPolynomial indices j T).natDegree ≤ bound := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  exact coeff_liftedNormalPolynomial_eq_zero_above indices j T bound n hbound hn

end Nagata.Workers.W17

end

section

/-!
# The actual homogeneous-monomial jet-matrix family
-/

namespace Nagata.Workers.W17

open scoped BigOperators
open Nagata.W27

variable {K : Type*} [CommRing K]

noncomputable def indexedPlaneFamily (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) : Polynomial (MvPolynomial (Fin 3) K) :=
  ∑ ν : HomogeneousMonomial d, (q ν).map MvPolynomial.C *
    Polynomial.C (MvPolynomial.monomial ν.val (1 : K))

theorem coeff_indexedPlaneFamily (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (α : Nat) :
    (indexedPlaneFamily d q).coeff α =
      ∑ ν : HomogeneousMonomial d, MvPolynomial.monomial ν.val ((q ν).coeff α) := by
  classical
  unfold indexedPlaneFamily
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, MvPolynomial.C_mul_monomial, mul_one]

theorem monomial_coeff_indexedPlaneFamily (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (α : Nat) (ν : HomogeneousMonomial d) :
    ((indexedPlaneFamily d q).coeff α).coeff ν.val = (q ν).coeff α := by
  classical
  rw [coeff_indexedPlaneFamily, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single ν]
  · simp
  · intro b hb hne
    simp only [ite_eq_right_iff]
    intro he
    exact (hne (Subtype.ext he)).elim
  · simp

theorem indexedPlaneFamily_homogeneous (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (α : Nat) :
    ((indexedPlaneFamily d q).coeff α).IsHomogeneous d := by
  rw [coeff_indexedPlaneFamily]
  apply MvPolynomial.IsHomogeneous.sum
  intro ν hν
  exact MvPolynomial.isHomogeneous_monomial _ ν.property

theorem indexedPlaneFamily_constant_ne_zero (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K)
    (hq : ∃ ν, (q ν).coeff 0 ≠ 0) :
    (indexedPlaneFamily d q).coeff 0 ≠ 0 := by
  obtain ⟨ν, hν⟩ := hq
  intro hz
  have h := monomial_coeff_indexedPlaneFamily d q 0 ν
  rw [hz, AddMonoidAlgebra.coeff_zero] at h
  exact hν h.symm

theorem eval_indexedPlaneFamily (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (s : K) :
    (indexedPlaneFamily d q).eval (MvPolynomial.C s) =
      ∑ ν : HomogeneousMonomial d, MvPolynomial.monomial ν.val ((q ν).eval s) := by
  classical
  unfold indexedPlaneFamily
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Polynomial.eval_mul, Polynomial.eval_map_apply, Polynomial.eval_C,
    MvPolynomial.C_mul_monomial, mul_one]

/-- The specialization is the exact form used by the finite jet matrix. -/
theorem eval_indexedPlaneFamily_eq_coordinates_symm (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (s : K) :
    (indexedPlaneFamily d q).eval (MvPolynomial.C s) =
      ((homogeneousCoordinates d).symm (fun ν => (q ν).eval s)).val := by
  classical
  rw [eval_indexedPlaneFamily]
  let F : MvPolynomial.homogeneousSubmodule (Fin 3) K d :=
    ⟨∑ ν : HomogeneousMonomial d, MvPolynomial.monomial ν.val ((q ν).eval s),
      MvPolynomial.IsHomogeneous.sum _ _ _
        (fun ν _ => MvPolynomial.isHomogeneous_monomial _ ν.property)⟩
  have hcoord : homogeneousCoordinates d F = fun ν => (q ν).eval s := by
    funext ν
    change F.val.coeff ν.val = (q ν).eval s
    dsimp only [F]
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single ν]
    · simp
    · intro b hb hne
      simp only [ite_eq_right_iff]
      intro he
      exact (hne (Subtype.ext he)).elim
    · simp
  have hF : F = (homogeneousCoordinates d).symm (fun ν => (q ν).eval s) := by
    apply (homogeneousCoordinates d).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hcoord
  exact congrArg Subtype.val hF

end Nagata.Workers.W17

end

section

/-!
# Degree-bounded initial polynomial of an actual plane-form family

This assembles maximal equation-divisibility, homogeneous quotient degrees,
and noncancellation. The output retains actual plane-polynomial lifts Tα,
not merely abstract sections. The geometric normal-bundle and order limits
are not asserted by this algebraic theorem.
-/

namespace Nagata.Workers.W17

open scoped BigOperators

variable {K : Type*} [Field K]

/-- All algebraic initial-form data, including actual homogeneous lifts and
floor(d/k) bounds, are constructed from a genuine polynomial family. -/
theorem exists_degree_bounded_plane_initial
    (S : Polynomial (MvPolynomial (Fin 3) K))
    (G : MvPolynomial (Fin 3) K) (d k : Nat)
    (hcoeff : ∀ α, (S.coeff α).IsHomogeneous d)
    (hG : G.IsHomogeneous k) (hunit : ¬IsUnit G) (hk : 0 < k)
    (hzero : S.coeff 0 ≠ 0) :
    ∃ (j : Nat → Nat) (T : Nat → MvPolynomial (Fin 3) K) (u : Nat),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α ∈ S.support, ¬G ∣ T α) ∧
      (∀ α ∈ S.support, j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α)) ∧
      (∀ α ∈ S.support, u ≤ α + j α) ∧
      u ≤ d / k ∧
      (S.support.filter (fun α => α + j α = u)).Nonempty ∧
      (∑ α ∈ S.support.filter (fun α => α + j α = u),
        Polynomial.monomial (j α)
          (Ideal.Quotient.mk
            (Ideal.span ({G} : Set (MvPolynomial (Fin 3) K))) (T α))) ≠ 0 := by
  classical
  have hS : S ≠ 0 := by
    intro hS
    apply hzero
    rw [hS, Polynomial.coeff_zero]
  obtain ⟨j, T, u, hfactor, hnot, hmin, hselected, hinitial⟩ :=
    exists_nonzero_normal_initial S G hS hunit
  have hdegree : ∀ α ∈ S.support,
      j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α) := by
    intro α hα
    have hn : S.coeff α ≠ 0 := Polynomial.mem_support_iff.mp hα
    exact ⟨homogeneous_power_exponent_bound (hcoeff α) hG hn (hfactor α) hk,
      (homogeneous_power_remainder (hcoeff α) hG hn (hfactor α)).2⟩
  have hu : u ≤ d / k :=
    (initial_weight_bound_from_constant S j u hzero hmin).trans
      (hdegree 0 (Polynomial.mem_support_iff.mpr hzero)).1
  exact ⟨j, T, u, hfactor, hnot, hdegree, hmin, hu, hselected, hinitial⟩

end Nagata.Workers.W17

end

section

/-! Grouping the selected actual homogeneous lifts by normal degree preserves
exact coefficient degrees, including zero coefficients and unequal labels. -/

namespace Nagata.Workers.W17

variable {K σ : Type*} [CommRing K]

/-- Actual grouped plane coefficients have exactly the manuscript's degree. -/
theorem homogeneous_coeff_liftedNormalPolynomial
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → MvPolynomial σ K)
    (d k : Nat) (hT : ∀ α ∈ indices, (T α).IsHomogeneous (d - k * j α))
    (n : Nat) :
    ((liftedNormalPolynomial indices j T).coeff n).IsHomogeneous (d - k * n) := by
  rw [coeff_liftedNormalPolynomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro α hα
  have hmem := (Finset.mem_filter.mp hα).1
  have heq := (Finset.mem_filter.mp hα).2
  simpa only [heq] using hT α hmem

/-- Every nonzero coefficient has an exponent within the selected degree bound. -/
theorem nonzero_coeff_liftedNormalPolynomial_bound
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → MvPolynomial σ K)
    (bound n : Nat) (hbound : ∀ α ∈ indices, j α ≤ bound)
    (hne : (liftedNormalPolynomial indices j T).coeff n ≠ 0) : n ≤ bound := by
  apply Nat.le_of_not_gt
  intro hn
  exact hne (coeff_liftedNormalPolynomial_eq_zero_above indices j T bound n hbound hn)

end Nagata.Workers.W17

end

section

/-! Exact polynomial reconstruction in each genuine affine projective chart. -/
namespace Nagata.Workers.W17
open scoped BigOperators

/-- Dehomogenizing a factored homogeneous family yields exactly the finite
G-adic polynomial family consumed by analytic normal specialization. -/
theorem directChart_factored_family
    (S : Polynomial (MvPolynomial (Fin 3) ℂ))
    (G : MvPolynomial (Fin 3) ℂ) (j : ℕ → ℕ)
    (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (hfactor : ∀ α, S.coeff α = G ^ j α * T α)
    (c : Fin 3) (s : ℂ) :
    Nagata.W27.directChartHom c (S.eval (MvPolynomial.C s)) =
      Nagata.Workers.W28.factoredPlaneFamily S.support j
        (fun α => Nagata.W27.directChartHom c (T α))
        (Nagata.W27.directChartHom c G) s := by
  classical
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum Nagata.Workers.W28.factoredPlaneFamily
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [hfactor, map_mul, map_mul, map_pow, map_pow]
  simp only [Nagata.W27.directChartHom, MvPolynomial.eval₂Hom_C, map_pow]
  ring

end Nagata.Workers.W17

end

end OAI
