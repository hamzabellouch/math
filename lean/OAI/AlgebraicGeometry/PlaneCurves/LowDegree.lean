import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import OAI.AlgebraicGeometry.PlaneCurves.HomogeneousFamilies
import OAI.AlgebraicGeometry.PlaneCurves.TorusConfigurations

namespace OAI

/-!
# Nonzero low-degree homogeneous equations and configurations
-/

section

/-!
# Reduced-triangle algebraic low-degree obstruction
-/
noncomputable section
namespace Nagata.W03.LowDegree
open Polynomial
open Nagata.W04.ReducibleSquare

variable {K : Type*} [Field K]

/-- Actual normal polynomial restricted to component i, with coefficients in
its affine coordinate ring K[U]. The outer polynomial variable is the fiber. -/
def lineNormalPolynomial (R : ℕ → MvPolynomial (Fin 3) K) (d i : ℕ) :
    Polynomial (Polynomial K) :=
  ∑ j ∈ Finset.range (d / 3 + 1),
    Polynomial.monomial j (lineRestriction (i : K) (R j))

/-- The ordinary fiber polynomial above the affine point with parameter U. -/
def fiberPolynomial (R : ℕ → MvPolynomial (Fin 3) K) (d i : ℕ) (U : K) : K[X] :=
  (lineNormalPolynomial R d i).map (Polynomial.evalRingHom U)

/-- Nine marked multiplicity conditions annihilate every coefficient below m
when d≤3m, including the equality-degree case on the reduced triangle. -/
theorem lower_coefficient_restrictions_zero [CharZero K]
    (R : ℕ → MvPolynomial (Fin 3) K) (d m : ℕ) (hdm : d ≤ 3 * m)
    (hdegree : ∀ j ≤ d / 3, ∀ i : ℕ, i < 3 →
      (lineRestriction (i : K) (R j)).natDegree ≤ d - 3 * j)
    (hfirst : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 →
      (X + C ((firstMark 3 i : ℕ) : K)) ^ (m - j) ∣ lineRestriction (i : K) (R j))
    (htail : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 → ∀ s < 2,
      (X + C ((s + 2 : ℕ) : K)) ^ (m - j) ∣ lineRestriction (i : K) (R j)) :
    ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 → lineRestriction (i : K) (R j) = 0 := by
  intro j hj hjm
  apply ambient_restrictions_zero 3 (m - j) (by decide) (by omega) (R j)
  · intro i hi
    exact (hdegree j hj i hi).trans (by omega)
  · exact hfirst j hj hjm
  · simpa using htail j hj hjm

/-- If d<3m all component normal polynomials vanish. This conclusion involves
actual polynomials, not a formal coefficient-vanishing predicate. -/
theorem strict_low_degree_lineNormal_zero
    (R : ℕ → MvPolynomial (Fin 3) K) (d m : ℕ) (hdm : d < 3 * m)
    (hlower : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 →
      lineRestriction (i : K) (R j) = 0) :
    ∀ i : ℕ, i < 3 → lineNormalPolynomial R d i = 0 := by
  intro i hi
  unfold lineNormalPolynomial
  apply Finset.sum_eq_zero
  intro j hj
  have hjd : j ≤ d / 3 := by simpa using hj
  have hjm : j < m := by omega
  rw [hlower j hjd hjm i hi, map_zero]

/-- At d=3m, vanishing of all lower coefficients leaves the actual top monomial. -/
theorem equality_lineNormal_shape
    (R : ℕ → MvPolynomial (Fin 3) K) (m : ℕ) (a : K)
    (hlower : ∀ j < m, ∀ i : ℕ, i < 3 → lineRestriction (i : K) (R j) = 0)
    (htop : R m = MvPolynomial.C a) :
    ∀ i : ℕ, i < 3 → lineNormalPolynomial R (3 * m) i = Polynomial.monomial m (C a) := by
  intro i hi
  unfold lineNormalPolynomial
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
  rw [Finset.sum_range_succ]
  have hsum : (∑ j ∈ Finset.range m,
      Polynomial.monomial j (lineRestriction (i : K) (R j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hlower j (Finset.mem_range.mp hj) i hi, map_zero]
  rw [hsum, zero_add, htop]
  congr 1
  simp [lineRestriction]

/-- Evaluation in the base coordinate preserves the top monomial and its scalar. -/
theorem equality_fiber_shape
    (R : ℕ → MvPolynomial (Fin 3) K) (m i : ℕ) (U a : K)
    (hshape : lineNormalPolynomial R (3 * m) i = Polynomial.monomial m (C a)) :
    fiberPolynomial R (3 * m) i U = Polynomial.monomial m a := by
  simp [fiberPolynomial, hshape]

/-- A pure nonzero top monomial cannot have positive root order at a nonzero
fiber displacement. The divisibility premise is ordinary polynomial multiplicity. -/
theorem pure_fiber_root_forces_scalar_zero (m : ℕ) (hm : 0 < m) (a c : K)
    (hc : c ≠ 0) (hroot : (X - C c) ^ m ∣ Polynomial.monomial m a) : a = 0 := by
  obtain ⟨q, hq⟩ := hroot
  have hval := congrArg (Polynomial.eval c) hq
  have haz : a * c ^ m = 0 := by simpa [Nat.ne_of_gt hm] using hval
  exact (mul_eq_zero.mp haz).resolve_right (pow_ne_zero m hc)

theorem equality_low_degree_contradiction
    (R : ℕ → MvPolynomial (Fin 3) K) (m : ℕ) (hm : 0 < m) (a U c : K)
    (hlower : ∀ j < m, ∀ i : ℕ, i < 3 → lineRestriction (i : K) (R j) = 0)
    (htop : R m = MvPolynomial.C a)
    (hnonzero : ∃ i < 3, lineNormalPolynomial R (3 * m) i ≠ 0)
    (hc : c ≠ 0)
    (hroot : (X - C c) ^ m ∣ fiberPolynomial R (3 * m) 0 U) : False := by
  have hshape := equality_lineNormal_shape R m a hlower htop
  have hfiber := equality_fiber_shape R m 0 U a (hshape 0 (by decide))
  rw [hfiber] at hroot
  have ha := pure_fiber_root_forces_scalar_zero m hm a c hc hroot
  obtain ⟨i, hi, hne⟩ := hnonzero
  apply hne
  rw [hshape i hi, ha, Polynomial.C_0, map_zero]

/-- Combined low-degree branch: these actual coefficient and fiber conditions
force d>3m. The top-constant condition follows from homogeneous degree zero. -/
theorem degree_gt_three_mul_of_normal_polynomial [CharZero K]
    (R : ℕ → MvPolynomial (Fin 3) K) (d m : ℕ) (hm : 0 < m) (U c : K)
    (hdegree : ∀ j ≤ d / 3, ∀ i : ℕ, i < 3 →
      (lineRestriction (i : K) (R j)).natDegree ≤ d - 3 * j)
    (hfirst : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 →
      (X + C ((firstMark 3 i : ℕ) : K)) ^ (m - j) ∣ lineRestriction (i : K) (R j))
    (htail : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 → ∀ s < 2,
      (X + C ((s + 2 : ℕ) : K)) ^ (m - j) ∣ lineRestriction (i : K) (R j))
    (htop : d = 3 * m → ∃ a : K, R m = MvPolynomial.C a)
    (hnonzero : ∃ i < 3, lineNormalPolynomial R d i ≠ 0)
    (hc : c ≠ 0)
    (hroot : (X - C c) ^ m ∣ fiberPolynomial R d 0 U) : 3 * m < d := by
  by_contra h
  have hdm : d ≤ 3 * m := by omega
  have hlower := lower_coefficient_restrictions_zero R d m hdm hdegree hfirst htail
  rcases lt_or_eq_of_le hdm with hlt | heq
  · obtain ⟨i, hi, hne⟩ := hnonzero
    exact hne (strict_low_degree_lineNormal_zero R d m hlt hlower i hi)
  · obtain ⟨a, ha⟩ := htop heq
    subst d
    apply equality_low_degree_contradiction R m hm a U c _ ha hnonzero hc hroot
    intro j hj i hi
    exact hlower j (by omega) hj i hi

/-- The ambient total-degree bounds discharge both the component-degree premise
and the common constant leading coefficient. Genuine homogeneous degree bounds
imply these total-degree bounds; no smooth-curve section theorem is used. -/
theorem degree_gt_three_mul_of_ambient_normal_polynomial [CharZero K]
    (R : ℕ → MvPolynomial (Fin 3) K) (d m : ℕ) (hm : 0 < m) (U c : K)
    (hdegree : ∀ j ≤ d / 3, (R j).totalDegree ≤ d - 3 * j)
    (hfirst : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 →
      (X + C ((firstMark 3 i : ℕ) : K)) ^ (m - j) ∣ lineRestriction (i : K) (R j))
    (htail : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 → ∀ s < 2,
      (X + C ((s + 2 : ℕ) : K)) ^ (m - j) ∣ lineRestriction (i : K) (R j))
    (hnonzero : ∃ i < 3, lineNormalPolynomial R d i ≠ 0)
    (hc : c ≠ 0)
    (hroot : (X - C c) ^ m ∣ fiberPolynomial R d 0 U) : 3 * m < d := by
  apply degree_gt_three_mul_of_normal_polynomial R d m hm U c _ hfirst htail _
    hnonzero hc hroot
  · intro j hj i hi
    exact (Nagata.W02.lineRestriction_natDegree_le_totalDegree (i : K) (R j)).trans
      (hdegree j hj)
  · intro hd
    have hmdegree : (R m).totalDegree = 0 := by
      have h := hdegree m (by omega)
      omega
    exact ⟨(R m).coeff 0, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hmdegree⟩

end Nagata.W03.LowDegree

end
end

section

noncomputable section
namespace Nagata.W03.LowDegree
open Polynomial
open Nagata.W04.ReducibleSquare
variable {K : Type*} [Field K]

/-- Normal polynomial with coefficients in the actual coordinate ring modulo G. -/
def quotientNormalPolynomial (R : ℕ → MvPolynomial (Fin 3) K) (d : ℕ)
    (G : MvPolynomial (Fin 3) K) :
    Polynomial (MvPolynomial (Fin 3) K ⧸ Ideal.span ({G} : Set (MvPolynomial (Fin 3) K))) :=
  ∑ j ∈ Finset.range (d / 3 + 1), Polynomial.monomial j
    (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) K))) (R j))

/-- A nonzero quotient normal polynomial has an actual nonzero residue coefficient. -/
theorem exists_nondivisible_coefficient_of_quotientNormal_ne_zero
    (R : ℕ → MvPolynomial (Fin 3) K) (d : ℕ) (G : MvPolynomial (Fin 3) K)
    (hN : quotientNormalPolynomial R d G ≠ 0) :
    ∃ j ≤ d / 3, ¬ G ∣ R j := by
  by_contra h
  push Not at h
  apply hN
  unfold quotientNormalPolynomial
  apply Finset.sum_eq_zero
  intro j hj
  have hdiv := h j (by simpa using hj)
  have hzero : Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) K)))
      (R j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  rw [hzero, map_zero]

/-- The j-th coefficient of the actual component polynomial is its line restriction. -/
theorem coeff_lineNormalPolynomial
    (R : ℕ → MvPolynomial (Fin 3) K) (d i j : ℕ) (hj : j ≤ d / 3) :
    (lineNormalPolynomial R d i).coeff j = lineRestriction (i : K) (R j) := by
  classical
  simp [lineNormalPolynomial, Polynomial.coeff_monomial,
    Finset.mem_range.mpr (show j < d / 3 + 1 by omega)]

/-- A proved component-noncancellation bridge transports the genuine quotient
nonzero condition to a nonzero component normal polynomial. -/
theorem exists_nonzero_lineNormal_of_quotientNormal_ne_zero
    (R : ℕ → MvPolynomial (Fin 3) K) (d : ℕ) (G : MvPolynomial (Fin 3) K)
    (hN : quotientNormalPolynomial R d G ≠ 0)
    (hcomponents : ∀ j ≤ d / 3, ¬ G ∣ R j →
      ∃ i : ℕ, i < 3 ∧ lineRestriction (i : K) (R j) ≠ 0) :
    ∃ i < 3, lineNormalPolynomial R d i ≠ 0 := by
  obtain ⟨j, hj, hdiv⟩ := exists_nondivisible_coefficient_of_quotientNormal_ne_zero R d G hN
  obtain ⟨i, hi, hres⟩ := hcomponents j hj hdiv
  refine ⟨i, hi, ?_⟩
  intro hzero
  apply hres
  rw [← coeff_lineNormalPolynomial R d i j hj, hzero, Polynomial.coeff_zero]

/-- The finite quotient sum agrees with mapping the actual normal polynomial
when its coefficient support obeys the source exponent bound. -/
theorem quotientNormalPolynomial_coeff_eq_map
    (F : Polynomial (MvPolynomial (Fin 3) K)) (d : ℕ) (G : MvPolynomial (Fin 3) K)
    (hbound : ∀ j, d / 3 < j → F.coeff j = 0) :
    quotientNormalPolynomial F.coeff d G =
      F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) K)))) := by
  classical
  ext j
  by_cases hj : j ≤ d / 3
  · simp [quotientNormalPolynomial, Polynomial.coeff_monomial,
      Finset.mem_range.mpr (show j < d / 3 + 1 by omega)]
  · have hjgt : d / 3 < j := by omega
    simp [quotientNormalPolynomial, Polynomial.coeff_monomial,
      (show ¬ j < d / 3 + 1 by omega), hbound j hjgt]

theorem quotientNormalPolynomial_ne_zero_of_map_ne_zero
    (F : Polynomial (MvPolynomial (Fin 3) K)) (d : ℕ) (G : MvPolynomial (Fin 3) K)
    (hbound : ∀ j, d / 3 < j → F.coeff j = 0)
    (hN : F.map (Ideal.Quotient.mk
      (Ideal.span ({G} : Set (MvPolynomial (Fin 3) K)))) ≠ 0) :
    quotientNormalPolynomial F.coeff d G ≠ 0 := by
  rwa [quotientNormalPolynomial_coeff_eq_map F d G hbound]

end Nagata.W03.LowDegree

end
end

section

/-! Convert actual point-ideal-power multiplicity conditions into the low-degree
coefficient and fiber obstruction. This discharges the coefficient-order step
at zero normal displacement with no highest-coefficient restriction. -/
noncomputable section
namespace Nagata.W03.LowDegree
open Polynomial
open Nagata.W04.ReducibleSquare Nagata.W18
variable {K : Type*} [Field K]

/-- The marked surface orders at zero displacement give the exact first and
tail root-factor conditions needed by the triangle coefficient obstruction. -/
theorem marked_factors_of_zero_surface_orders
    (R : ℕ → MvPolynomial (Fin 3) K) (d m : ℕ)
    (hfirst : ∀ i < 3, lineNormalPolynomial R d i ∈
      (nestedPointIdeal (-((firstMark 3 i : ℕ) : K)) 0) ^ m)
    (htail : ∀ i < 3, ∀ s < 2, lineNormalPolynomial R d i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : K)) 0) ^ m) :
    (∀ j ≤ d / 3, ∀ i : ℕ, i < 3 →
      (X + C ((firstMark 3 i : ℕ) : K)) ^ (m - j) ∣ lineRestriction (i : K) (R j)) ∧
    (∀ j ≤ d / 3, ∀ i : ℕ, i < 3 → ∀ s < 2,
      (X + C ((s + 2 : ℕ) : K)) ^ (m - j) ∣ lineRestriction (i : K) (R j)) := by
  constructor
  · intro j hj i hi
    have h := all_coefficients_base_divisibility_at_zero (lineNormalPolynomial R d i)
      (-((firstMark 3 i : ℕ) : K)) m (hfirst i hi) j
    simpa only [coeff_lineNormalPolynomial R d i j hj, map_neg, sub_neg_eq_add] using h
  · intro j hj i hi s hs
    have h := all_coefficients_base_divisibility_at_zero (lineNormalPolynomial R d i)
      (-((s + 2 : ℕ) : K)) m (htail i hi s hs) j
    simpa only [coeff_lineNormalPolynomial R d i j hj, map_neg, sub_neg_eq_add] using h

theorem degree_gt_three_mul_of_surface_orders [CharZero K]
    (R : ℕ → MvPolynomial (Fin 3) K) (d m : ℕ) (hm : 0 < m) (U c : K)
    (hdegree : ∀ j ≤ d / 3, (R j).totalDegree ≤ d - 3 * j)
    (hfirst : ∀ i < 3, lineNormalPolynomial R d i ∈
      (nestedPointIdeal (-((firstMark 3 i : ℕ) : K)) 0) ^ m)
    (htail : ∀ i < 3, ∀ s < 2, lineNormalPolynomial R d i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : K)) 0) ^ m)
    (hnonzero : ∃ i < 3, lineNormalPolynomial R d i ≠ 0) (hc : c ≠ 0)
    (htenth : lineNormalPolynomial R d 0 ∈ (nestedPointIdeal U c) ^ m) : 3 * m < d := by
  have hfactors := marked_factors_of_zero_surface_orders R d m hfirst htail
  apply degree_gt_three_mul_of_ambient_normal_polynomial R d m hm U c hdegree
    (fun j hj _ => hfactors.1 j hj) (fun j hj _ => hfactors.2 j hj) hnonzero hc
  exact fiber_power_divides_of_surface_order (lineNormalPolynomial R d 0) U c m htenth

end Nagata.W03.LowDegree

end
end

section

noncomputable section
namespace Nagata.W03.LowDegree
open Polynomial
open Nagata.W04.ReducibleSquare

/-- Homogeneous noncancellation turns the genuine quotient normal polynomial
into a nonzero polynomial on at least one actual affine line component. -/
theorem exists_nonzero_lineNormal_of_homogeneous_quotient
    (R : ℕ → MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hhom : ∀ j ≤ d / 3, (R j).IsHomogeneous (d - 3 * j))
    (hN : quotientNormalPolynomial R d (Nagata.Workers.W24.homogeneousLineUnion ℂ 3) ≠ 0) :
    ∃ i < 3, lineNormalPolynomial R d i ≠ 0 := by
  apply exists_nonzero_lineNormal_of_quotientNormal_ne_zero R d
    (Nagata.Workers.W24.homogeneousLineUnion ℂ 3) hN
  intro j hj hdiv
  obtain ⟨i, hi⟩ := Nagata.Workers.W24.exists_nonzero_affine_lineRestriction
    3 (d - 3 * j) (R j) (hhom j hj) hdiv
  exact ⟨i.val, i.isLt, hi⟩

/-- The complete algebraic low-degree branch over the genuine three-line
homogeneous curve. The first nine multiplicity conditions are actual root
factors; the tenth condition is ordinary fiber-polynomial root multiplicity. -/
theorem degree_gt_three_mul_of_homogeneous_normal_polynomial
    (R : ℕ → MvPolynomial (Fin 3) ℂ) (d m : ℕ) (hm : 0 < m) (U c : ℂ)
    (hhom : ∀ j ≤ d / 3, (R j).IsHomogeneous (d - 3 * j))
    (hfirst : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 →
      (X + C ((firstMark 3 i : ℕ) : ℂ)) ^ (m - j) ∣ lineRestriction (i : ℂ) (R j))
    (htail : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 → ∀ s < 2,
      (X + C ((s + 2 : ℕ) : ℂ)) ^ (m - j) ∣ lineRestriction (i : ℂ) (R j))
    (hN : quotientNormalPolynomial R d (Nagata.Workers.W24.homogeneousLineUnion ℂ 3) ≠ 0)
    (hc : c ≠ 0)
    (hroot : (X - C c) ^ m ∣ fiberPolynomial R d 0 U) : 3 * m < d := by
  apply degree_gt_three_mul_of_ambient_normal_polynomial R d m hm U c
    (fun j hj => (hhom j hj).totalDegree_le) hfirst htail
    (exists_nonzero_lineNormal_of_homogeneous_quotient R d hhom hN) hc hroot

theorem degree_gt_three_mul_of_grouped_homogeneous_normal_polynomial
    (F : Polynomial (MvPolynomial (Fin 3) ℂ)) (d m : ℕ) (hm : 0 < m) (U c : ℂ)
    (hbound : ∀ j, d / 3 < j → F.coeff j = 0)
    (hhom : ∀ j ≤ d / 3, (F.coeff j).IsHomogeneous (d - 3 * j))
    (hfirst : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 →
      (X + C ((firstMark 3 i : ℕ) : ℂ)) ^ (m - j) ∣ lineRestriction (i : ℂ) (F.coeff j))
    (htail : ∀ j ≤ d / 3, j < m → ∀ i : ℕ, i < 3 → ∀ s < 2,
      (X + C ((s + 2 : ℕ) : ℂ)) ^ (m - j) ∣ lineRestriction (i : ℂ) (F.coeff j))
    (hN : F.map (Ideal.Quotient.mk (Ideal.span
      ({Nagata.Workers.W24.homogeneousLineUnion ℂ 3} : Set (MvPolynomial (Fin 3) ℂ)))) ≠ 0)
    (hc : c ≠ 0)
    (hroot : (X - C c) ^ m ∣ fiberPolynomial F.coeff d 0 U) : 3 * m < d := by
  exact degree_gt_three_mul_of_homogeneous_normal_polynomial F.coeff d m hm U c
    hhom hfirst htail (quotientNormalPolynomial_ne_zero_of_map_ne_zero F d
      (Nagata.Workers.W24.homogeneousLineUnion ℂ 3) hbound hN) hc hroot

/-- Final reduced-triangle algebraic low-degree statement: actual homogeneous
coefficient lifts, actual quotient nonzero polynomial, and ordinary point-ideal
powers at the nine zero and one nonzero normal displacements imply d>3m. -/
theorem degree_gt_three_mul_of_homogeneous_surface_orders
    (R : ℕ → MvPolynomial (Fin 3) ℂ) (d m : ℕ) (hm : 0 < m) (U c : ℂ)
    (hhom : ∀ j ≤ d / 3, (R j).IsHomogeneous (d - 3 * j))
    (hfirst : ∀ i < 3, lineNormalPolynomial R d i ∈
      (Nagata.W18.nestedPointIdeal (-((firstMark 3 i : ℕ) : ℂ)) 0) ^ m)
    (htail : ∀ i < 3, ∀ s < 2, lineNormalPolynomial R d i ∈
      (Nagata.W18.nestedPointIdeal (-((s + 2 : ℕ) : ℂ)) 0) ^ m)
    (hN : quotientNormalPolynomial R d (Nagata.Workers.W24.homogeneousLineUnion ℂ 3) ≠ 0)
    (hc : c ≠ 0)
    (htenth : lineNormalPolynomial R d 0 ∈ (Nagata.W18.nestedPointIdeal U c) ^ m) :
    3 * m < d :=
  degree_gt_three_mul_of_surface_orders R d m hm U c
    (fun j hj => (hhom j hj).totalDegree_le) hfirst htail
    (exists_nonzero_lineNormal_of_homogeneous_quotient R d hhom hN) hc htenth

end Nagata.W03.LowDegree

end
end

section

/-!
# Low-degree contradiction on the actual every-r triangle configuration
-/
noncomputable section
namespace Nagata.W03.LowDegree
open Polynomial
open Nagata.W04.ReducibleSquare Nagata.W06.LineArrangement Nagata.Workers.W17

abbrev TriangleIndex (r : ℕ) := (Fin 3 × Fin 3) ⊕ Fin (r - 9)

def triangleComponent {r : ℕ} : TriangleIndex r → ℕ :=
  Sum.elim (fun p => p.1.val) (fun _ => 0)

def triangleBasePoint (r : ℕ) : TriangleIndex r → ℂ × ℂ :=
  mixedPoint ℂ 3 (r - 9)

def triangleDisplacement {r : ℕ} : TriangleIndex r → ℂ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

/-- This actual ordered index set has exactly r distinct base points. -/
theorem triangle_configuration_count_and_injective (r : ℕ) (hr : 9 ≤ r) :
    Fintype.card (TriangleIndex r) = r ∧ Function.Injective (triangleBasePoint r) := by
  constructor
  · simp only [TriangleIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  · exact mixedPoint_injective 3 (r - 9)

/-- On the actual r-point configuration, surface orders of the normal
polynomial force d>3m; the case r=10 and all larger r are treated uniformly. -/
theorem degree_gt_three_mul_on_triangle_configuration
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (R : ℕ → MvPolynomial (Fin 3) ℂ)
    (hhom : ∀ j ≤ d / 3, (R j).IsHomogeneous (d - 3 * j))
    (hN : quotientNormalPolynomial R d (Nagata.Workers.W24.homogeneousLineUnion ℂ 3) ≠ 0)
    (horder : ∀ p : TriangleIndex r,
      lineNormalPolynomial R d (triangleComponent p) ∈
        (Nagata.W18.nestedPointIdeal (triangleBasePoint r p).1 (triangleDisplacement p)) ^ m) :
    3 * m < d := by
  refine degree_gt_three_mul_of_homogeneous_surface_orders R d m hm (-5) 1 hhom ?_ ?_ hN
    (by norm_num) ?_
  · intro i hi
    have h := horder (Sum.inl ((⟨i, hi⟩ : Fin 3), (⟨0, by decide⟩ : Fin 3)))
    simpa [triangleComponent, triangleBasePoint, triangleDisplacement, mixedPoint,
      markedPoint, markedCoordinate] using h
  · intro i hi s hs
    have h := horder (Sum.inl ((⟨i, hi⟩ : Fin 3), (⟨s + 1, by omega⟩ : Fin 3)))
    have hneg : (-1 : ℂ) + -1 = -2 := by norm_num
    simpa [triangleComponent, triangleBasePoint, triangleDisplacement, mixedPoint,
      markedPoint, markedCoordinate, Nat.add_assoc, ← add_assoc, hneg] using h
  · have h := horder (Sum.inr (⟨0, by omega⟩ : Fin (r - 9)))
    simpa [triangleComponent, triangleBasePoint, triangleDisplacement, mixedPoint,
      extraPoint] using h

theorem degree_gt_three_mul_of_selected_lifts_on_triangle
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (indices : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ) (u : ℕ)
    (hne : indices.Nonempty) (hweight : ∀ α ∈ indices, α + j α = u)
    (hnot : ∀ α ∈ indices, ¬ Nagata.Workers.W24.homogeneousLineUnion ℂ 3 ∣ T α)
    (hbound : ∀ α ∈ indices, j α ≤ d / 3)
    (hhom : ∀ α ∈ indices, (T α).IsHomogeneous (d - 3 * j α))
    (horder : ∀ p : TriangleIndex r,
      lineNormalPolynomial (liftedNormalPolynomial indices j T).coeff d (triangleComponent p) ∈
        (Nagata.W18.nestedPointIdeal (triangleBasePoint r p).1 (triangleDisplacement p)) ^ m) :
    3 * m < d := by
  apply degree_gt_three_mul_on_triangle_configuration r d m hr hm
    (liftedNormalPolynomial indices j T).coeff
  · intro n hn
    exact homogeneous_coeff_liftedNormalPolynomial indices j T d 3 hhom n
  · apply quotientNormalPolynomial_ne_zero_of_map_ne_zero
      (liftedNormalPolynomial indices j T) d
      (Nagata.Workers.W24.homogeneousLineUnion ℂ 3)
    · intro n hn
      exact coeff_liftedNormalPolynomial_eq_zero_above indices j T (d / 3) n hbound hn
    · exact quotient_liftedNormalPolynomial_ne_zero indices j T
        (Nagata.Workers.W24.homogeneousLineUnion ℂ 3) u hne hweight hnot
  · exact horder

end Nagata.W03.LowDegree

end
end

end OAI
