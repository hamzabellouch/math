import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothRealActionModel
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegerSemidirectLattice

namespace OAI

/-! # A cyclic lattice in a smooth real-action extension

The remaining algebraic obligation in an application is to construct the
real action with the stated time-one automorphism.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology

variable {H L : Type} [Group H] [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L] [Group L] [LieGroup (𝓘(ℝ, L)) ⊤ L]
  [Group.IsSolvable L]

theorem smooth_realAction_cyclic_lattice
    (φ : Multiplicative ℝ →* MulAut L)
    (hφ : ContDiff ℝ ⊤ (fun p : ℝ × L => φ (Multiplicative.ofAdd p.1) p.2))
    (a : MulAut H) (Λ : Subgroup L) (hΛ : IsUniformLattice Λ) (e : H ≃* Λ)
    (he : ∀ x, (e (a x) : L) = φ (Multiplicative.ofAdd 1) (e x)) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧
        Nonempty ((H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ) := by
  obtain ⟨Γ, hΓ, ⟨f⟩⟩ := integer_semidirect_lattice_realization φ a Λ hΛ e he
  let S := smoothRealActionModel φ hφ
  let E := smoothRealActionModelEquiv φ hφ
  refine ⟨S, Γ.comap E.toMonoidHom, ?_, ⟨f.trans (comapSubgroupEquiv E Γ).symm⟩⟩
  exact hΓ.comap_mulEquiv E (smoothRealActionModelEquiv_continuous φ hφ)
    (smoothRealActionModelEquiv_symm_continuous φ hφ)

end PolycyclicRecognition

end

end OAI
