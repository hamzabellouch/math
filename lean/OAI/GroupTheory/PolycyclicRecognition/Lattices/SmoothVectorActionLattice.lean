import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothVectorActionModel
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SemidirectLatticeEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticeGenerators
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeTransport

namespace OAI

/-! # Integral lattices in smooth vector-action extensions -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology
variable {H L : Type} [Group H] [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L] [Group L] [LieGroup (𝓘(ℝ, L)) ⊤ L] [Group.IsSolvable L]

theorem smooth_vectorAction_integral_lattice {n : ℕ}
    (φ : Multiplicative (Fin n → ℝ) →* MulAut L)
    (hφ : ContDiff ℝ ⊤ (fun p : (Fin n → ℝ) × L => φ (Multiplicative.ofAdd p.1) p.2))
    (ρ : IntegralLatticeGroup n →* MulAut H)
    (Λ : Subgroup L) (hΛ : IsUniformLattice Λ) (e : H ≃* Λ)
    (he : ∀ z x, (e (ρ z x) : L) = φ (integerVectorHom n z) (e x)) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧ Nonempty ((H ⋊[ρ] IntegralLatticeGroup n) ≃* Γ) := by
  obtain ⟨Γ, hΓ, ⟨f⟩⟩ := semidirect_lattice_embedding ρ φ Λ (integerVectorHom n).range
    e (integerVectorRangeEquiv n) he hΛ (integerVectorHom_uniform n)
  let S := smoothVectorActionModel φ hφ
  let E := smoothVectorActionModelEquiv φ hφ
  refine ⟨S, Γ.comap E.toMonoidHom, ?_, ⟨f.trans (comapSubgroupEquiv E Γ).symm⟩⟩
  exact hΓ.comap_mulEquiv E (smoothVectorActionModelEquiv_continuous φ hφ)
    (smoothVectorActionModelEquiv_symm_continuous φ hφ)

end PolycyclicRecognition

end

end OAI
