import OAI.Analysis.KadisonKastler.PublishedIndependence
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

/-! # The trace projection onto a finite dimensional base

Nondegeneracy of the trace pairing on a finite dimensional star algebra
constructs the projection onto that algebra. Only its range and pairing
properties are needed for the finite word argument.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

private def baseTracePairing (τ : FaithfulTracialState B) (D : StarSubalgebra ℂ B) :
    B →ₗ[ℂ] Module.Dual ℂ D where
  toFun x :=
    { toFun := fun b => τ.toLinearMap ((b : B) * x)
      map_add' := by intros; simp only [AddMemClass.coe_add, add_mul, map_add]
      map_smul' := by intros; simp only [SetLike.val_smul, smul_mul_assoc, map_smul,
        RingHom.id_apply] }
  map_add' x y := by
    ext b
    change τ.toLinearMap ((b : B) * (x + y)) =
      τ.toLinearMap ((b : B) * x) + τ.toLinearMap ((b : B) * y)
    rw [mul_add, map_add]
  map_smul' z x := by
    ext b
    change τ.toLinearMap ((b : B) * (z • x)) = z • τ.toLinearMap ((b : B) * x)
    rw [mul_smul_comm, map_smul]

private theorem baseTracePairing_injective (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) :
    Function.Injective ((baseTracePairing τ D).comp D.toSubmodule.subtype) := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply τ.faithful
  have hd : star ((x : B) - y) ∈ D := D.star_mem' (D.sub_mem x.property y.property)
  have he := congrArg (fun f : Module.Dual ℂ D => f ⟨_, hd⟩) h
  change τ.toLinearMap (star ((x : B) - y) * x) =
    τ.toLinearMap (star ((x : B) - y) * y) at he
  rw [mul_sub, map_sub, he, sub_self]

private def baseTracePairingEquiv (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] : D ≃ₗ[ℂ] Module.Dual ℂ D :=
  LinearMap.linearEquivOfInjective ((baseTracePairing τ D).comp D.toSubmodule.subtype)
    (baseTracePairing_injective τ D) (by rw [Subspace.dual_finrank_eq])

/-- The actual trace projection, defined by solving the finite trace-pairing
system. No conditional expectation existence theorem is assumed. -/
def finiteBaseExpectation (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] : B →ₗ[ℂ] B :=
  D.toSubmodule.subtype.comp
    ((baseTracePairingEquiv τ D).symm.toLinearMap.comp (baseTracePairing τ D))

theorem finiteBaseExpectation_mem (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] (x : B) :
    finiteBaseExpectation τ D x ∈ D :=
  ((baseTracePairingEquiv τ D).symm (baseTracePairing τ D x)).property

theorem finiteBaseExpectation_pairing (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] (x : B) {b : B} (hb : b ∈ D) :
    τ.toLinearMap (b * finiteBaseExpectation τ D x) = τ.toLinearMap (b * x) := by
  exact congrArg (fun f : Module.Dual ℂ D => f ⟨b, hb⟩)
    ((baseTracePairingEquiv τ D).apply_symm_apply (baseTracePairing τ D x))

theorem finiteBaseExpectation_trace (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] (x : B) :
    τ.toLinearMap (finiteBaseExpectation τ D x) = τ.toLinearMap x := by
  simpa only [one_mul] using finiteBaseExpectation_pairing τ D x D.one_mem

theorem finiteBaseExpectation_fixed (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] {x : B} (hx : x ∈ D) :
    finiteBaseExpectation τ D x = x := by
  exact congrArg (fun b : D => (b : B))
    ((baseTracePairingEquiv τ D).symm_apply_apply ⟨x, hx⟩)

theorem finiteBaseExpectation_zero_iff (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] (x : B) :
    finiteBaseExpectation τ D x = 0 ↔ TraceOrthogonal τ D x := by
  constructor
  · intro he b hb
    rw [← finiteBaseExpectation_pairing τ D x hb, he, mul_zero, map_zero]
  · intro hx
    apply τ.faithful
    rw [finiteBaseExpectation_pairing τ D x (D.star_mem' (finiteBaseExpectation_mem τ D x))]
    exact hx _ (D.star_mem' (finiteBaseExpectation_mem τ D x))

theorem traceOrthogonal_sub_finiteBaseExpectation (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] (x : B) :
    TraceOrthogonal τ D (x - finiteBaseExpectation τ D x) := by
  intro b hb
  rw [mul_sub, map_sub, finiteBaseExpectation_pairing τ D x hb, sub_self]

end

end KadisonKastler

end OAI
