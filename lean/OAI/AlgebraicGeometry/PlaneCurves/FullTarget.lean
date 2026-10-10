import OAI.AlgebraicGeometry.PlaneCurves.BasisNoncancellation
import OAI.AlgebraicGeometry.PlaneCurves.CubicEquations
import OAI.AlgebraicGeometry.PlaneCurves.Incidence
import OAI.AlgebraicGeometry.PlaneCurves.SquareReduction

namespace OAI

/-!
# Coordinate and ordinary-multiplicity assemblies of the full target
-/

section

/-!
# Equivalent full statements using numerical ordinary multiplicity

Local ideal-power multiplicity bounds are equivalent to inequalities for
the numerical ordinary multiplicity of a nonzero homogeneous equation.
-/
noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators

/-- The unchanged full baseline quantifier pattern, with each multiplicity
lower bound written as an inequality between actual natural numbers. -/
def FullNagataOrdinary : Prop :=
  ∀ r : ℕ, 10 ≤ r →
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ (F : MvPolynomial (Fin 3) ℂ) (hFne : F ≠ 0) (hFhom : F.IsHomogeneous d),
        ∀ m : Fin r → ℕ,
          (∀ i, m i ≤ formOrdinaryMultiplicity ⟨F, hFhom, hFne⟩ (p.val i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt (r : ℝ)

/-- Numerical ordinary multiplicity gives exactly the original lower-bound
predicate at every point, hence exactly the full baseline proposition. -/
theorem fullNagata_iff_ordinary : Nagata.FullNagata ↔ FullNagataOrdinary := by
  constructor
  · intro h r hr
    obtain ⟨E, hEclosed, hEnonempty, hbound⟩ := h r hr
    refine ⟨E, hEclosed, hEnonempty, ?_⟩
    intro p hp d hd F hFne hFhom m hm
    apply hbound p hp d hd F hFne hFhom m
    intro i
    exact (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity
      ⟨F, hFhom, hFne⟩ (p.val i) (m i)).mpr (hm i)
  · intro h r hr
    obtain ⟨E, hEclosed, hEnonempty, hbound⟩ := h r hr
    refine ⟨E, hEclosed, hEnonempty, ?_⟩
    intro p hp d hd F hFne hFhom m hm
    apply hbound p hp d hd F hFne hFhom m
    intro i
    exact (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity
      ⟨F, hFhom, hFne⟩ (p.val i) (m i)).mp (hm i)

/-- The equivalent numerical formulation for projective classes of nonzero
homogeneous equations. Classes identify only nonzero scalar multiples, not
zero loci or radicals; reducible and nonreduced equations remain represented. -/
def FullNagataClassOrdinary : Prop :=
  ∀ r : ℕ, 10 ≤ r →
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ C : W16.PlaneEquationClass d,
        ∀ m : Fin r → ℕ,
          (∀ i, m i ≤ classOrdinaryMultiplicity C (p.val i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt (r : ℝ)

/-- Passing between a nonzero equation and its scalar class preserves its
numerical ordinary multiplicity and the very same exceptional sequence. -/
theorem ordinary_iff_classOrdinary : FullNagataOrdinary ↔ FullNagataClassOrdinary := by
  constructor
  · intro h r hr
    obtain ⟨E, hEclosed, hEnonempty, hbound⟩ := h r hr
    refine ⟨E, hEclosed, hEnonempty, ?_⟩
    intro p hp d hd C m hm
    exact hbound p hp d hd (W16.classRepresentative C).polynomial
      (W16.classRepresentative C).nonzero (W16.classRepresentative C).homogeneous m hm
  · intro h r hr
    obtain ⟨E, hEclosed, hEnonempty, hbound⟩ := h r hr
    refine ⟨E, hEclosed, hEnonempty, ?_⟩
    intro p hp d hd F hFne hFhom m hm
    apply hbound p hp d hd (W16.classOfForm ⟨F, hFhom, hFne⟩) m
    intro i
    rw [classOrdinaryMultiplicity_classOfForm]
    exact hm i

theorem fullNagata_iff_classOrdinary : Nagata.FullNagata ↔ FullNagataClassOrdinary :=
  fullNagata_iff_ordinary.trans ordinary_iff_classOrdinary

end Nagata.W13

end
end

section

/-!
# Strict very-general square case

This is the square-point-count restriction of the original full target. The
single exceptional sequence handles every positive degree and every nonnegative
unequal multiplicity vector. The actual projective closedness, countable
avoidance, and strict universal-system exclusion are all supplied by checked
proofs; no `hno` or other geometric assumption remains in these statements.
-/
noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators

/-- For `k≥4`, one proper closed exceptional sequence with nonempty complement
handles all curves and unequal multiplicity vectors at `k²` projective points.
This assembles the already-proved outside-union inequality without reproving it. -/
theorem square_veryGeneral (k : ℕ) (hk : 4 ≤ k) :
    ∃ E : ℕ → Set (OrderedDistinctPoints (k * k)),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints (k * k), ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints (k * k), (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 → F.IsHomogeneous d →
        ∀ m : Fin (k * k) → ℕ,
          (∀ i, multiplicityAtLeast F (p.val i) (m i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt ((k * k : ℕ) : ℝ) := by
  obtain ⟨E, hEclosed, hEnonempty, hEavoid⟩ :=
    Workers.W25.exists_closed_exceptional_sequence (supportLocus (k * k))
      (supportLocus_isConfigurationZariskiClosed (k * k))
  refine ⟨E, hEclosed, hEnonempty, ?_⟩
  intro p hp d hd F hFne hFhom m hm
  exact Workers.W24.square_strict_inequality_outside_supportExceptionalUnion
    k hk p ((hEavoid p).mp hp) d hd m F hFne hFhom hm

/-- Exactly the original target's quantifiers, restricted explicitly to square
`r≥10`; no restriction to uniform multiplicities or reduced equations appears. -/
theorem square_veryGeneral_of_isSquare (r : ℕ) (hr : 10 ≤ r) (hsquare : IsSquare r) :
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 → F.IsHomogeneous d →
        ∀ m : Fin r → ℕ,
          (∀ i, multiplicityAtLeast F (p.val i) (m i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt (r : ℝ) := by
  obtain ⟨k, hk⟩ := hsquare
  have hk4 := Workers.W14.square_root_ge_four hr hk
  subst r
  exact square_veryGeneral k hk4

/-- The same square result using actual natural-number ordinary multiplicities,
while preserving every raw polynomial and multiplicity-vector quantifier. -/
theorem square_veryGeneral_ordinary (r : ℕ) (hr : 10 ≤ r) (hsquare : IsSquare r) :
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ (F : MvPolynomial (Fin 3) ℂ) (hFne : F ≠ 0) (hFhom : F.IsHomogeneous d),
        ∀ m : Fin r → ℕ,
          (∀ i, m i ≤ formOrdinaryMultiplicity ⟨F, hFhom, hFne⟩ (p.val i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt (r : ℝ) := by
  obtain ⟨E, hEclosed, hEnonempty, hbound⟩ := square_veryGeneral_of_isSquare r hr hsquare
  refine ⟨E, hEclosed, hEnonempty, ?_⟩
  intro p hp d hd F hFne hFhom m hm
  apply hbound p hp d hd F hFne hFhom m
  intro i
  exact (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity
    ⟨F, hFhom, hFne⟩ (p.val i) (m i)).mpr (hm i)

/-- The same strict square theorem for scalar classes of equations and numerical
ordinary multiplicities. Classes identify scalar multiples, not radicals. -/
theorem square_veryGeneral_classOrdinary (r : ℕ) (hr : 10 ≤ r) (hsquare : IsSquare r) :
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ C : W16.PlaneEquationClass d,
        ∀ m : Fin r → ℕ,
          (∀ i, m i ≤ classOrdinaryMultiplicity C (p.val i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt (r : ℝ) := by
  obtain ⟨E, hEclosed, hEnonempty, hbound⟩ := square_veryGeneral_ordinary r hr hsquare
  refine ⟨E, hEclosed, hEnonempty, ?_⟩
  intro p hp d hd C m hm
  exact hbound p hp d hd (W16.classRepresentative C).polynomial
    (W16.classRepresentative C).nonzero (W16.classRepresentative C).homogeneous m hm

end Nagata.W13

end
end

section

/-!
Projective closedness, countable avoidance, the strict square case and the cubic
lower endpoint reduce the full inequality to exclusion of positive universal
systems in the nonsquare open interval.
-/
noncomputable section
namespace Nagata.W13

/-- Once genuine universal systems in the nonsquare interior are excluded,
the unchanged original full coordinate target follows. Every other branch and
the single simultaneous exceptional sequence are supplied by checked proofs. -/
theorem fullNagata_of_nonsquare_interior_exclusion
    (hinterior : ∀ r : ℕ, 10 ≤ r → ¬ IsSquare r → ∀ d m : ℕ,
      0 < d → 0 < m → 3 < (d : ℝ) / m → (d : ℝ) / m < Real.sqrt r →
      ¬ UniversalSupport r d (fun _ => m)) : Nagata.FullNagata := by
  intro r hr
  by_cases hsquare : IsSquare r
  · exact square_veryGeneral_of_isSquare r hr hsquare
  · apply strict_bound_of_no_universal r hr
    intro d m hd hm hbound hU
    have hlow := Nagata.W03.LowDegree.cubic_low_degree r d m hr hd hm hU
    have hrange := Workers.W14.elliptic_ratio_range hsquare hm hlow hbound
    exact hinterior r hr hsquare d m hd hm hrange.1 hrange.2 hU

/-- The same conditional assembly concludes the proved-equivalent formulation
with numerical ordinary multiplicities and identical original quantifiers. -/
theorem fullNagataOrdinary_of_nonsquare_interior_exclusion
    (hinterior : ∀ r : ℕ, 10 ≤ r → ¬ IsSquare r → ∀ d m : ℕ,
      0 < d → 0 < m → 3 < (d : ℝ) / m → (d : ℝ) / m < Real.sqrt r →
      ¬ UniversalSupport r d (fun _ => m)) : FullNagataOrdinary :=
  fullNagata_iff_ordinary.mp (fullNagata_of_nonsquare_interior_exclusion hinterior)

end Nagata.W13

end
end

section

noncomputable section
open Filter Topology
open scoped BigOperators
namespace Nagata.W13
open Nagata.Workers.W10 Nagata.Workers.W12 Nagata.W20 Nagata.FiniteExponents Nagata.W22 Nagata.CoefficientSpaces Nagata.W29

theorem fullNagata_of_genuine_source_construction
    (hconstruction : ∀ r : ℕ, 10 ≤ r → ¬ IsSquare r → ∀ d m : ℕ,
      0 < d → 0 < m → 3 < (d : ℝ) / m → (d : ℝ) / m < Real.sqrt r →
      UniversalSupport r d (fun _ => m) →
      ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ (hτ : 0 < τ) (hτone : τ < 1) (U : Set ℂ),
          IsOpen U ∧ (0 : ℂ) ∈ U ∧
          (∀ p : Fin (r - 9) → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
            ∃ F : genuineSourceSections hτ hτone x (3 * (Real.sqrt r - 3))
                ((n * d : ℕ) : ℤ) (n * m),
              F ≠ 0 ∧ ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
                (fun z : ℂ × ℂ => localScalar F (tauPower τ (1 / 2)) z.1 z.2)
                (p i, 0) (n * m))) : Nagata.FullNagata := by
  apply fullNagata_of_nonsquare_interior_exclusion
  intro r hr hns d m hd hm hlow hupp hU
  exact Workers.W12.genuine_source_geometric_contradiction r d m hr hm hlow hupp
    (hconstruction r hr hns d m hd hm hlow hupp hU)

end Nagata.W13

end
end

end OAI
