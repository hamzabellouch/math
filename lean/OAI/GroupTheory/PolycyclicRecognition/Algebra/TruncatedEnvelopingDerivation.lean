import OAI.GroupTheory.PolycyclicRecognition.Algebra.TruncatedEnvelopingAlgebra

namespace OAI

/-! # Derivations on the finite truncated enveloping algebra -/

noncomputable section
namespace PolycyclicRecognition

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "Q" => TruncatedEnvelopingAlgebra R L

def truncatedEnvelopingDerivation (c : ℕ) (D : LieDerivation R L L) : Q c →ₗ[R] Q c where
  toFun := Quotient.map' (envelopingDerivation D) (by
    intro x y hxy
    apply ((envelopingTruncationIdeal (R := R) c).rel_iff _ _).mpr
    rw [← map_sub]
    exact envelopingDerivation_preserves_truncation D c
      (((envelopingTruncationIdeal (R := R) c).rel_iff _ _).mp hxy))
  map_add' x y := Quotient.inductionOn₂ x y fun a b => by
    change truncatedEnvelopingProjection c (envelopingDerivation D (a + b)) =
      truncatedEnvelopingProjection c (envelopingDerivation D a) +
      truncatedEnvelopingProjection c (envelopingDerivation D b)
    rw [map_add, map_add]
  map_smul' r x := Quotient.inductionOn x fun a => by
    change truncatedEnvelopingProjection c (envelopingDerivation D (r • a)) =
      r • truncatedEnvelopingProjection c (envelopingDerivation D a)
    rw [map_smul, map_smul]

@[simp]
theorem truncatedEnvelopingDerivation_projection (c : ℕ) (D : LieDerivation R L L) (u : U) :
    truncatedEnvelopingDerivation c D (truncatedEnvelopingProjection c u) =
      truncatedEnvelopingProjection c (envelopingDerivation D u) := rfl

@[simp]
theorem truncatedEnvelopingDerivation_generator (c : ℕ) (D : LieDerivation R L L) (x : L) :
    truncatedEnvelopingDerivation c D (truncatedEnvelopingGenerator c x) =
      truncatedEnvelopingGenerator c (D x) := by
  change truncatedEnvelopingProjection c
    (envelopingDerivation D (UniversalEnvelopingAlgebra.ι R x)) = _
  rw [envelopingDerivation_generator]
  rfl

theorem truncatedEnvelopingDerivation_mul (c : ℕ) (D : LieDerivation R L L) (x y : Q c) :
    truncatedEnvelopingDerivation c D (x * y) =
      x * truncatedEnvelopingDerivation c D y + truncatedEnvelopingDerivation c D x * y := by
  obtain ⟨a, rfl⟩ := truncatedEnvelopingProjection_surjective c x
  obtain ⟨b, rfl⟩ := truncatedEnvelopingProjection_surjective c y
  rw [← map_mul, truncatedEnvelopingDerivation_projection, envelopingDerivation_mul,
    map_add, map_mul, map_mul, truncatedEnvelopingDerivation_projection,
    truncatedEnvelopingDerivation_projection]

def truncatedEnvelopingDerivationRepresentation (c : ℕ) :
    LieDerivation R L L →ₗ⁅R⁆ Module.End R (Q c) where
  toFun := truncatedEnvelopingDerivation c
  map_add' D E := by
    ext x
    obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective c x
    simp only [LinearMap.add_apply, truncatedEnvelopingDerivation_projection,
      envelopingDerivation_add, map_add]
  map_smul' r D := by
    ext x
    obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective c x
    simp only [LinearMap.smul_apply, truncatedEnvelopingDerivation_projection,
      envelopingDerivation_smul, map_smul, RingHom.id_apply]
  map_lie' {D E} := by
    ext x
    obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective c x
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      truncatedEnvelopingDerivation_projection, envelopingDerivation_lie, map_sub]

end PolycyclicRecognition

end

end OAI
