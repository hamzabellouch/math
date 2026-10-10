import OAI.Geometry.HeilbronnTriangle.IntegralPlaneReduction
import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice

namespace OAI


noncomputable section
namespace Problem355.RealPlaneReduction
open IntegralPlaneReduction
open scoped LinearAlgebra.Projectivization

def kernelEquiv (Λ : Submodule ℤ Vector) (x : Vector) :
    integralPlane Λ x ≃ₗ[ℤ] IntegralPlaneLattice.latticeIn x Λ :=
  IntegralPlaneLattice.kernelEquivIn x Λ

def reductionHom (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector) (x : Vector) :
    IntegralPlaneLattice.latticeIn x Λ →+
      (PlaneLines.normalMap (reducedNormal q x)).ker :=
  (IntegralPlaneReduction.reductionHom q Λ x).comp (kernelEquiv Λ x).symm.toAddMonoidHom

theorem reductionHom_surjective (q : ℕ) [Fact q.Prime]
    (Λ : Submodule ℤ Vector) (x z : Vector) (hz : dotProduct x z = 1)
    (E : ℤ) (hE : IsUnit (E : ZMod q)) (hΛ : ∀ w : Vector, E • w ∈ Λ) :
    Function.Surjective (reductionHom q Λ x) :=
  (IntegralPlaneReduction.reductionHom_surjective q Λ x z hz E hE hΛ).comp
    (kernelEquiv Λ x).symm.surjective

@[simp] theorem reductionHom_kernelEquiv (q : ℕ) [Fact q.Prime]
    (Λ : Submodule ℤ Vector) (x : Vector) (v : integralPlane Λ x) :
    reductionHom q Λ x (kernelEquiv Λ x v) =
      IntegralPlaneReduction.reductionHom q Λ x v := by
  simp [reductionHom]

theorem cast_kernelEquiv_symm (Λ : Submodule ℤ Vector) (x : Vector)
    (v : IntegralPlaneLattice.latticeIn x Λ) :
    IntegralPlaneLattice.castVec ((kernelEquiv Λ x).symm v : Vector) =
      ((v : IntegralPlaneLattice.plane x) : IntegralPlaneLattice.Ambient) := by
  exact congrArg (fun w : IntegralPlaneLattice.latticeIn x Λ =>
    ((w : IntegralPlaneLattice.plane x) : IntegralPlaneLattice.Ambient))
    ((kernelEquiv Λ x).apply_symm_apply v)

theorem line_preimage_index (q : ℕ) [Fact q.Prime]
    (Λ : Submodule ℤ Vector) (x z : Vector) (hz : dotProduct x z = 1)
    (E : ℤ) (hE : IsUnit (E : ZMod q)) (hΛ : ∀ w : Vector, E • w ∈ Λ)
    (p : ℙ (ZMod q) (PlaneLines.normalMap (reducedNormal q x)).ker) :
    (p.submodule.toAddSubgroup.comap (reductionHom q Λ x)).index = q := by
  have h := PlaneLines.line_preimage_index
    (PlaneLines.normal_plane_finrank (reducedNormal q x) (reducedNormal_ne_zero q x z hz))
    (reductionHom q Λ x) (reductionHom_surjective q Λ x z hz E hE hΛ) p
  simpa [Nat.card_eq_fintype_card, ZMod.card] using h

def equalCoordinateLattice (q : ℕ) [Fact q.Prime]
    (Λ : Submodule ℤ Vector) (x : Vector) (i j : Fin 3) :
    AddSubgroup (IntegralPlaneLattice.latticeIn x Λ) :=
  (PlaneFunctional.equalCoordinateSubgroup q (integralPlane Λ x).toAddSubgroup i j).comap
    (kernelEquiv Λ x).symm.toAddMonoidHom

@[simp] theorem mem_equalCoordinateLattice (q : ℕ) [Fact q.Prime]
    (Λ : Submodule ℤ Vector) (x : Vector) (i j : Fin 3)
    (v : IntegralPlaneLattice.latticeIn x Λ) :
    v ∈ equalCoordinateLattice q Λ x i j ↔
      (reductionHom q Λ x v : Fin 3 → ZMod q) i =
        (reductionHom q Λ x v : Fin 3 → ZMod q) j := by
  change (kernelEquiv Λ x).symm v ∈
    PlaneFunctional.equalCoordinateSubgroup q (integralPlane Λ x).toAddSubgroup i j ↔ _
  rw [PlaneFunctional.mem_equalCoordinateSubgroup]
  rfl

theorem equalCoordinateLattice_index (q : ℕ) [Fact q.Prime]
    (Λ : Submodule ℤ Vector) (x z : Vector) (hz : dotProduct x z = 1)
    (E : ℤ) (hE : IsUnit (E : ZMod q)) (hΛ : ∀ w : Vector, E • w ∈ Λ)
    (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q,
      reducedNormal q x = a • PlaneFunctional.coordinateDifference i j) :
    (equalCoordinateLattice q Λ x i j).index = q := by
  rw [equalCoordinateLattice,
    AddSubgroup.index_comap_of_surjective _ (kernelEquiv Λ x).symm.surjective]
  exact IntegralPlaneReduction.equalCoordinate_index q Λ x z hz E hE hΛ i j hij hspan

end Problem355.RealPlaneReduction

end

end OAI
