import OAI.GroupTheory.PolycyclicRecognition.Algebra.HilbertOrbitAverage
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.GroupTheory.Subgroup.Center

namespace OAI

/-! # The central fixed subspace in a unitary representation

The central fixed subspace is closed and invariant under the whole group.
Its orthogonal projection therefore commutes with the representation. These
are the concrete splitting facts for the nilpotent cohomology induction.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E))

def unitaryCentralFixed : Submodule ℝ E where
  carrier := {x | ∀ z : Subgroup.center G, ρ z x = x}
  zero_mem' := fun z => map_zero (ρ z)
  add_mem' hx hy z := by rw [map_add, hx z, hy z]
  smul_mem' c x hx z := by rw [map_smul, hx z]

theorem isClosed_unitaryCentralFixed : IsClosed (unitaryCentralFixed ρ : Set E) := by
  have h := isClosed_iInter (fun z : Subgroup.center G =>
    isClosed_eq (ρ z).continuous continuous_id)
  convert h using 1
  ext x
  simp [unitaryCentralFixed]

theorem unitaryCentralFixed_map (g : G) {x : E} (hx : x ∈ unitaryCentralFixed ρ) :
    ρ g x ∈ unitaryCentralFixed ρ := by
  intro z
  have hz := Subgroup.mem_center_iff.mp z.property g
  calc
    ρ z (ρ g x) = ρ ((z : G) * g) x := by rw [map_mul]; rfl
    _ = ρ (g * (z : G)) x := by rw [hz]
    _ = ρ g (ρ z x) := by rw [map_mul]; rfl
    _ = ρ g x := by rw [hx z]

theorem unitaryCentralFixed_map_eq (g : G) :
    (unitaryCentralFixed ρ).map (ρ g).toLinearEquiv.toLinearMap = unitaryCentralFixed ρ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact unitaryCentralFixed_map ρ g hx
  · intro hy
    refine ⟨ρ g⁻¹ y, unitaryCentralFixed_map ρ g⁻¹ hy, ?_⟩
    change ρ g (ρ g⁻¹ y) = y
    have he : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f y) he

theorem unitaryCentralFixed_orthogonal_map (g : G) {x : E}
    (hx : x ∈ (unitaryCentralFixed ρ)ᗮ) : ρ g x ∈ (unitaryCentralFixed ρ)ᗮ := by
  have he := (unitaryCentralFixed ρ).map_orthogonal_equiv (ρ g)
  rw [unitaryCentralFixed_map_eq ρ g] at he
  rw [← he]
  exact Submodule.mem_map_of_mem hx

theorem unitaryCentralFixed_orthogonal_no_fixed
    (v : (unitaryCentralFixed ρ)ᗮ)
    (hv : ∀ z : Subgroup.center G, ρ z (v : E) = v) : v = 0 := by
  apply Subtype.ext
  have hm : (v : E) ∈ unitaryCentralFixed ρ := hv
  exact inner_self_eq_zero.mp (v.property (v : E) hm)

instance unitaryCentralFixed_complete [CompleteSpace E] : CompleteSpace (unitaryCentralFixed ρ) :=
  (isClosed_unitaryCentralFixed ρ).completeSpace_coe

theorem unitaryCentralFixed_projection_commutes [CompleteSpace E] (g : G) (x : E) :
    ρ g ((unitaryCentralFixed ρ).starProjection x) =
      (unitaryCentralFixed ρ).starProjection (ρ g x) := by
  have hm : (unitaryCentralFixed ρ).map (ρ g).toLinearIsometry.toLinearMap =
      unitaryCentralFixed ρ := unitaryCentralFixed_map_eq ρ g
  have : ((unitaryCentralFixed ρ).map (ρ g).toLinearIsometry.toLinearMap).HasOrthogonalProjection :=
    hm.symm ▸ inferInstance
  have h := (ρ g).toLinearIsometry.map_starProjection (unitaryCentralFixed ρ) x
  simpa only [hm, LinearIsometryEquiv.coe_toLinearIsometry] using h

end PolycyclicRecognition

end

end OAI
