import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Extending Lie derivations to the enveloping algebra

The square-zero extension constructs the associative Leibniz extension. This
will act on the finite truncated enveloping representation of the nilradical.
-/

noncomputable section
namespace PolycyclicRecognition

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "η" => UniversalEnvelopingAlgebra.ι R (L := L)

/-- Induction on scalar elements and Lie generators. -/
@[elab_as_elim]
theorem enveloping_induction {P : U → Prop}
    (hscalar : ∀ r, P (algebraMap R U r)) (hgen : ∀ x, P (η x))
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hmul : ∀ a b, P a → P b → P (a * b)) (u : U) : P u := by
  obtain ⟨v, rfl⟩ := RingCon.mkₐ_surjective (α := R)
    (UniversalEnvelopingAlgebra.ringCon R L) u
  induction v using TensorAlgebra.induction with
  | algebraMap r => exact hscalar r
  | ι x => exact hgen x
  | add a b ha hb => exact hadd _ _ ha hb
  | mul a b ha hb => exact hmul _ _ ha hb

def envelopingDerivationLift (D : LieDerivation R L L) :
    L →ₗ⁅R⁆ TrivSqZeroExt U U where
  toFun x := ⟨η x, η (D x)⟩
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change η (x + y) = η x + η y
      exact map_add _ _ _
    · change η (D (x + y)) = η (D x) + η (D y)
      simp only [map_add]
  map_smul' r x := by
    apply TrivSqZeroExt.ext
    · change η (r • x) = r • η x
      exact map_smul _ _ _
    · change η (D (r • x)) = r • η (D x)
      simp only [map_smul]
  map_lie' {x y} := by
    apply TrivSqZeroExt.ext
    · exact (η).map_lie x y
    · change η (D ⁅x, y⁆) = _
      rw [D.apply_lie_eq_sub, map_sub, (η).map_lie, (η).map_lie]
      change (η x * η (D y) - η (D y) * η x) -
        (η y * η (D x) - η (D x) * η y) =
        (η x * η (D y) + η (D x) * η y) -
        (η y * η (D x) + η (D y) * η x)
      abel

theorem envelopingDerivationLift_fst (D : LieDerivation R L L) :
    (TrivSqZeroExt.fstHom R U U).comp
      (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D)) = AlgHom.id R U := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext x
  change (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) (η x)).fst = η x
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The unique associative derivation extending the given Lie derivation. -/
def envelopingDerivation (D : LieDerivation R L L) : U →ₗ[R] U :=
  (TrivSqZeroExt.sndHom U U).restrictScalars R ∘ₗ
    (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D)).toLinearMap

@[simp]
theorem envelopingDerivation_generator (D : LieDerivation R L L) (x : L) :
    envelopingDerivation D (η x) = η (D x) := by
  change TrivSqZeroExt.snd
    (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) (η x)) = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

@[simp]
theorem envelopingDerivation_scalar (D : LieDerivation R L L) (r : R) :
    envelopingDerivation D (algebraMap R U r) = 0 := by
  change TrivSqZeroExt.snd
    (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) (algebraMap R U r)) = _
  rw [AlgHom.commutes]
  rfl

theorem envelopingDerivation_mul (D : LieDerivation R L L) (a b : U) :
    envelopingDerivation D (a * b) =
      a * envelopingDerivation D b + envelopingDerivation D a * b := by
  have hf (x : U) :
      (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) x).fst = x :=
    DFunLike.congr_fun (envelopingDerivationLift_fst D) x
  change TrivSqZeroExt.snd
    (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) (a * b)) = _
  rw [map_mul, TrivSqZeroExt.snd_mul, hf, hf]
  rfl

theorem enveloping_derivation_ext (f g : U →ₗ[R] U)
    (hf : ∀ r, f (algebraMap R U r) = 0)
    (hg : ∀ r, g (algebraMap R U r) = 0)
    (hfm : ∀ a b, f (a * b) = a * f b + f a * b)
    (hgm : ∀ a b, g (a * b) = a * g b + g a * b)
    (hgen : ∀ x, f (η x) = g (η x)) : f = g := by
  ext u
  induction u using enveloping_induction with
  | hscalar r => rw [hf, hg]
  | hgen x => exact hgen x
  | hadd a b ha hb => simp only [map_add, ha, hb]
  | hmul a b ha hb => rw [hfm, hgm, ha, hb]

theorem envelopingDerivation_add (D E : LieDerivation R L L) :
    envelopingDerivation (D + E) = envelopingDerivation D + envelopingDerivation E := by
  apply enveloping_derivation_ext
  · exact envelopingDerivation_scalar _
  · intro r
    simp only [LinearMap.add_apply, envelopingDerivation_scalar, add_zero]
  · exact envelopingDerivation_mul _
  · intro a b
    simp only [LinearMap.add_apply, envelopingDerivation_mul]
    noncomm_ring
  · intro x
    simp only [envelopingDerivation_generator, LinearMap.add_apply,
      LieDerivation.add_apply, map_add]

theorem envelopingDerivation_smul (r : R) (D : LieDerivation R L L) :
    envelopingDerivation (r • D) = r • envelopingDerivation D := by
  apply enveloping_derivation_ext
  · exact envelopingDerivation_scalar _
  · intro t
    simp only [LinearMap.smul_apply, envelopingDerivation_scalar, smul_zero]
  · exact envelopingDerivation_mul _
  · intro a b
    simp only [LinearMap.smul_apply, envelopingDerivation_mul, smul_add,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  · intro x
    simp only [envelopingDerivation_generator, LinearMap.smul_apply,
      LieDerivation.smul_apply, map_smul]

theorem envelopingDerivation_lie (D E : LieDerivation R L L) :
    envelopingDerivation ⁅D, E⁆ = ⁅envelopingDerivation D, envelopingDerivation E⁆ := by
  apply enveloping_derivation_ext
  · exact envelopingDerivation_scalar _
  · intro r
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      envelopingDerivation_scalar, map_zero, sub_zero]
  · exact envelopingDerivation_mul _
  · intro a b
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      envelopingDerivation_mul, map_add]
    noncomm_ring
  · intro x
    simp only [envelopingDerivation_generator, Ring.lie_def, LinearMap.sub_apply,
      Module.End.mul_apply, LieDerivation.lie_apply, map_sub]

/-- Derivations act on the enveloping algebra by a Lie representation. -/
def envelopingDerivationRepresentation : LieDerivation R L L →ₗ⁅R⁆ Module.End R U where
  toFun := envelopingDerivation
  map_add' := envelopingDerivation_add
  map_smul' := envelopingDerivation_smul
  map_lie' {D E} := envelopingDerivation_lie D E

end PolycyclicRecognition

end

end OAI
