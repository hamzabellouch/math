import OAI.Analysis.Nonexpansive.OriginalNorm
import OAI.Analysis.Nonexpansive.Reduction
import OAI.Analysis.Nonexpansive.NormalizedContradiction

namespace OAI

/-!
# Fixed points in the original norm

The counterexample reduction constructs the actual normalized minimal data.
The adaptive tree, finite switching witnesses and whole-ball branch argument
then contradict those data.  The public statements use the given norm on the
original real Banach space, including the zero and nonseparable cases.
-/

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A real reflexive Banach space has the nonexpansive fixed point property
in its given norm. Reflexivity is canonical continuous-bidual surjectivity. -/
theorem hasNonexpansiveFixedPointProperty_of_canonicallyReflexive
    (hX : CanonicallyReflexive X) : HasNonexpansiveFixedPointProperty X := by
  intro C hne hclosed hbounded hconvex F hF
  by_contra hnone
  have hno : ∀ x : C, F x ≠ x := by
    intro x hx
    exact hnone ⟨x, hx⟩
  obtain ⟨D⟩ := exists_normalizedMinimalData_of_counterexample
    hX hne hclosed hbounded hconvex F
    ((nonexpansiveOn_iff_lipschitzWith_one C F).mp hF) hno
  exact normalizedMinimalData_false D

/-- Every nonexpansive selfmap of a nonempty closed bounded convex set has
an actual fixed point, with nonexpansiveness stated in the original norm. -/
theorem exists_fixedPoint_of_canonicallyReflexive
    (hX : CanonicallyReflexive X) (C : Set X)
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C)
    (hF : ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖) :
    ∃ a : C, F a = a :=
  hasNonexpansiveFixedPointProperty_of_canonicallyReflexive hX
    C hne hclosed hbounded hconvex F hF

/-- The equivalent metric formulation has Lipschitz constant one. -/
theorem exists_fixedPoint_of_lipschitzWith_one
    (hX : CanonicallyReflexive X) (C : Set X)
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C) (hF : LipschitzWith 1 F) :
    ∃ a : C, F a = a :=
  exists_fixedPoint_of_canonicallyReflexive hX C hne hclosed hbounded hconvex
    F ((nonexpansiveOn_iff_lipschitzWith_one C F).mpr hF)

/-- The ambient-map formulation asserts membership and the literal equation
for the original map. -/
theorem exists_ambient_fixedPoint_of_canonicallyReflexive
    (hX : CanonicallyReflexive X) (C : Set X)
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : X → X) (hmap : Set.MapsTo F C C)
    (hF : ∀ a ∈ C, ∀ b ∈ C, ‖F a - F b‖ ≤ ‖a - b‖) :
    ∃ a ∈ C, F a = a :=
  ambient_fixedPoint_of_property
    (hasNonexpansiveFixedPointProperty_of_canonicallyReflexive hX)
    C hne hclosed hbounded hconvex F hmap hF

end ReflexiveFixedPoints

end

end OAI
