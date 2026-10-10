import OAI.Analysis.Nonexpansive.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-!
# The fixed point property in the given norm

The public property quantifies over actual convex subsets and their selfmaps.
Its nonexpansiveness condition uses the existing ambient norm.  These elementary
interface lemmas neither change that norm nor supply the main reflexive-space
theorem; the latter is proved by the reduction and contradiction chain.
-/

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem nonexpansiveOn_iff_lipschitzWith_one {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (C : Set X) (F : C → C) :
    NonexpansiveOn C F ↔ LipschitzWith 1 F := by
  constructor
  · intro h
    apply LipschitzWith.mk_one
    intro a b
    simpa only [Subtype.dist_eq, dist_eq_norm] using h a b
  · intro h a b
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
      using h.dist_le_mul a b

/-- In particular, the property includes the zero space. -/
theorem hasNonexpansiveFixedPointProperty_of_subsingleton [Subsingleton X] :
    HasNonexpansiveFixedPointProperty X := by
  intro C hC _ _ _ F _
  obtain ⟨x, hx⟩ := hC
  exact ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩

/-- An ambient map preserving the set has the same fixed-point conclusion. -/
theorem ambient_fixedPoint_of_property
    (hX : HasNonexpansiveFixedPointProperty X)
    (C : Set X) (hC : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : X → X) (hmap : Set.MapsTo F C C)
    (hF : ∀ a ∈ C, ∀ b ∈ C, ‖F a - F b‖ ≤ ‖a - b‖) :
    ∃ a ∈ C, F a = a := by
  let f : C → C := fun a => ⟨F a, hmap a.property⟩
  have hf : NonexpansiveOn C f := fun a b => hF a a.property b b.property
  obtain ⟨a, ha⟩ := hX C hC hclosed hbounded hconvex f hf
  exact ⟨a, a.property, congrArg Subtype.val ha⟩

end ReflexiveFixedPoints

end

end OAI
