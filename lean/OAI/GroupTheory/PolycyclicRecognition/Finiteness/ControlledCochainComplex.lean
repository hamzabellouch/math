import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledFaceSupport
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI

/-! # The complex of controlled homogeneous cochains

The square-zero identity is inherited from the standard homogeneous resolution;
the support lemmas prove that its dual differential stays inside the controlled
cochains.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

variable {G R : Type} [Group G] [CommRing R] {n : ℕ}

def controlledLinearExtension (c : controlledCochains R G n) :
    MonoidAlgebra R (Fin (n + 1) → G) →ₗ[R] R :=
  (Finsupp.linearCombination R (fun x => c x)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem controlledLinearExtension_coboundary (c : controlledCochains R G n) :
    controlledLinearExtension (controlledCoboundary c) =
      (controlledLinearExtension c).comp (Rep.standardComplex.d R G (n + 1)) := by
  ext x
  simp [controlledLinearExtension, Rep.standardComplex.d_single,
    controlledCoboundary_apply, Finset.mul_sum]

private theorem standardBoundary_squared :
    (Rep.standardComplex.d R G (n + 1)).comp (Rep.standardComplex.d R G (n + 2)) = 0 := by
  apply LinearMap.ext
  intro v
  have h := (Rep.standardComplex R G).d_comp_d (n + 2) (n + 1) n
  have hv := congrArg (fun f : (Rep.standardComplex R G).X (n + 2) ⟶
      (Rep.standardComplex R G).X n => f.hom v) h
  change ((Rep.standardComplex R G).d (n + 1) n).hom
    (((Rep.standardComplex R G).d (n + 2) (n + 1)).hom v) = 0 at hv
  rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_apply] at hv
  exact hv

/-- The actual controlled coboundary squares to zero. -/
theorem controlledCoboundary_squared (c : controlledCochains R G n) :
    controlledCoboundary (controlledCoboundary c) = 0 := by
  have h : controlledLinearExtension (controlledCoboundary (controlledCoboundary c)) = 0 := by
    rw [controlledLinearExtension_coboundary, controlledLinearExtension_coboundary,
      LinearMap.comp_assoc, standardBoundary_squared, LinearMap.comp_zero]
  apply Subtype.ext
  funext x
  have hx := congrArg (fun f => f (MonoidAlgebra.single x 1)) h
  simpa [controlledLinearExtension] using hx

/-- Locally finite scalar homogeneous cochains, with the standard alternating differential. -/
def controlledCochainComplex (R G : Type) [CommRing R] [Group G] :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (controlledCochains R G n))
    (fun _ => ModuleCat.ofHom controlledCoboundary) (fun _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact controlledCoboundary_squared c)

@[simp] theorem controlledCochainComplex_d (n : ℕ) :
    (controlledCochainComplex R G).d n (n + 1) = ModuleCat.ofHom controlledCoboundary := by
  simp [controlledCochainComplex, CochainComplex.of.d]

end PolycyclicRecognition

end

end OAI
