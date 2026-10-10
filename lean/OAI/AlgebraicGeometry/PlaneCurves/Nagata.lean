import OAI.AlgebraicGeometry.PlaneCurves.FixedCurveSections
import OAI.AlgebraicGeometry.PlaneCurves.FullTarget

namespace OAI

/-!
# Nagata's inequality for very general complex plane configurations; Equivalence of homogeneous-coordinate and effective-cycle statements
-/

section

noncomputable section
namespace Nagata.Workers.W10
open Nagata.ProjectiveGeometry Nagata.W16
open scoped BigOperators

/-- Full strict simultaneous target on genuine nonzero effective curve cycles.
No square-only, equal-multiplicity, degree, or reducedness restriction is added. -/
def FullNagataCurves : Prop :=
  ∀ r : ℕ, 10 ≤ r →
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ C : EffectivePlaneCurve, ∀ m : Fin r → ℕ,
          (∀ i, curveMultiplicityAtLeast C (p.val i) (m i)) →
          (∑ i, (m i : ℝ)) < (curveDegree C : ℝ) * Real.sqrt (r : ℝ)

/-- Both full statements use exactly the same simultaneous exceptional union.
The proof transports degree and all local orders through the proved cycle bridge. -/
theorem fullNagata_iff_effectiveCurves : Nagata.FullNagata ↔ FullNagataCurves := by
  constructor
  · intro h r hr
    obtain ⟨E, hclosed, hnonempty, hbound⟩ := h r hr
    refine ⟨E, hclosed, hnonempty, ?_⟩
    intro p hp C m hm
    exact hbound p hp (curveDegree C) (curveDegree_pos C)
      (curveEquation C) (curveEquation_nonzero C) (curveEquation_homogeneous C) m hm
  · intro h r hr
    obtain ⟨E, hclosed, hnonempty, hbound⟩ := h r hr
    refine ⟨E, hclosed, hnonempty, ?_⟩
    intro p hp d hd F hF hhom m hm
    let form : NonzeroHomogeneousForm d := ⟨F, hhom, hF⟩
    let C := curveOfForm form hd
    have hcycle : Nagata.Workers.W30.equationIdealCycle F = C.val :=
      (curveOfForm_cycle form hd).symm
    have hmult : ∀ i, curveMultiplicityAtLeast C (p.val i) (m i) := by
      intro i
      exact (curveMultiplicityAtLeast_iff_equation C hF hcycle (p.val i) (m i)).mpr (hm i)
    have hb := hbound p hp C m hmult
    simpa only [C, curveOfForm_degree] using hb

end Nagata.Workers.W10

end
end

section

noncomputable section
namespace Nagata.Workers.W10
open Nagata.ProjectiveGeometry
open scoped BigOperators

/-- One exceptional union handles every genuine effective curve and every
unequal nonnegative multiplicity vector. All positive degrees, reducible curves
and repeated components remain quantified. -/
def FullNagataEffectiveCurves : Prop :=
  ∀ r : ℕ, 10 ≤ r →
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ C : EffectivePlaneCurve, ∀ m : Fin r → ℕ,
          (∀ i, m i ≤ Nagata.W15.curveOrdinaryMultiplicity C (p.val i)) →
          (∑ i, (m i : ℝ)) < (curveDegree C : ℝ) * Real.sqrt (r : ℝ)

theorem fullNagataCurves_iff_ordinary : FullNagataCurves ↔ FullNagataEffectiveCurves := by
  unfold FullNagataCurves FullNagataEffectiveCurves
  simp only [Nagata.W15.curveMultiplicityAtLeast_iff_le_ordinaryMultiplicity]

theorem fullNagata_iff_genuineEffectiveCurves :
    Nagata.FullNagata ↔ FullNagataEffectiveCurves :=
  fullNagata_iff_effectiveCurves.trans fullNagataCurves_iff_ordinary

end Nagata.Workers.W10

end
end

section

/-!
# Full Nagata theorem: final source assembly
-/
noncomputable section
namespace Nagata.W13

/-- The unchanged full coordinate statement, for every square and nonsquare
`r≥10`, all positive degrees, and all nonnegative unequal multiplicity vectors.
No geometric construction or universal-exclusion premise remains. -/
theorem nagata_full : Nagata.FullNagata := by
  apply fullNagata_of_genuine_source_construction
  intro r hr _hns d m _hd _hm _hlow _hupp hU
    n _delta x _hn _hdelta _hdeltahalf hxinj hxbounds _hxsum
    _hfirst _hsecond _hnonempty
  exact CoefficientSpaces.source_fixed_scaled_construction
    (le_trans (by decide : 9 ≤ 10) hr) hU n x hxinj hxbounds
    (3 * (Real.sqrt r - 3))

/-- Full numerical ordinary-multiplicity formulation for nonzero homogeneous
plane equations; the same simultaneous quantifier pattern is retained. -/
theorem nagata_full_ordinary : FullNagataOrdinary :=
  fullNagata_iff_ordinary.mp nagata_full

/-- Full numerical ordinary-multiplicity statement for scalar classes of
nonzero equations, retaining reducible and nonreduced structure. -/
theorem nagata_full_classOrdinary : FullNagataClassOrdinary :=
  fullNagata_iff_classOrdinary.mp nagata_full

/-- The full strict theorem for genuine nonzero effective plane-curve cycles,
with their actual degree and numerical ordinary multiplicities. -/
theorem nagata_full_effectiveCurves : Workers.W10.FullNagataEffectiveCurves :=
  Workers.W10.fullNagata_iff_genuineEffectiveCurves.mp nagata_full

end Nagata.W13

end
end

section

/-!
# Nagata conjecture for every number of very general complex plane points

Effective curves below are genuine nonzero finite cycles of homogeneous prime
plane ideals. Their degree and ordinary local multiplicities are independent
of the representing equation. Repeated components retain their coefficients.
The coordinate formulation is proved equivalent to this statement.
-/
noncomputable section
namespace Nagata
open ProjectiveGeometry
open scoped BigOperators

/-- One countable proper closed exceptional union works simultaneously for all
nonzero effective plane curves and all unequal nonnegative multiplicities. -/
theorem nagata_conjecture :
    ∀ r : ℕ, 10 ≤ r →
      ∃ E : ℕ → Set (OrderedDistinctPoints r),
        (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
        (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
        ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
          ∀ C : Workers.W10.EffectivePlaneCurve, ∀ m : Fin r → ℕ,
            (∀ i, m i ≤ W15.curveOrdinaryMultiplicity C (p.val i)) →
            (∑ i, (m i : ℝ)) <
              (Workers.W10.curveDegree C : ℝ) * Real.sqrt (r : ℝ) :=
  W13.nagata_full_effectiveCurves

/-- The original complete coordinate statement, including every degree d≥1,
all nonzero homogeneous equations and all nonnegative multiplicity bounds. -/
theorem nagata_conjecture_coordinates : FullNagata := W13.nagata_full

end Nagata

end
end

end OAI
