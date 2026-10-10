import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothVectorActionModel
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticeGenerators
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeEmbedding

namespace OAI

/-! # Cocompact embeddings of integral semidirect groups

A uniform lattice in the integral semidirect group may have translated
kernel fibers. No product-lattice assumption is required.
-/

noncomputable section
namespace PolycyclicRecognition
open Set
attribute [local instance] semidirectProductTopology

variable {L : Type} [Group L] [TopologicalSpace L]

private theorem integerVectorHom_isEmbedding (n : ℕ) :
    Topology.IsEmbedding (integerVectorHom n) := by
  let := (integerVectorHom_uniform n).1
  let e := integerVectorRangeEquiv n
  let h : IntegralLatticeGroup n ≃ₜ (integerVectorHom n).range :=
    { e.toEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact Topology.IsEmbedding.subtypeVal.comp h.isEmbedding

variable {n : ℕ} (ρ : IntegralLatticeGroup n →* MulAut L)
  (φ : Multiplicative (Fin n → ℝ) →* MulAut L)
  (hφ : ∀ z x, ρ z x = φ (integerVectorHom n z) x)

def integralSemidirectEmbedding :
    (L ⋊[ρ] IntegralLatticeGroup n) →* (L ⋊[φ] Multiplicative (Fin n → ℝ)) :=
  SemidirectProduct.map (MonoidHom.id L) (integerVectorHom n)
    (fun z => DFunLike.ext _ _ (hφ z))

theorem integralSemidirectEmbedding_isEmbedding :
    Topology.IsEmbedding (integralSemidirectEmbedding ρ φ hφ) := by
  have hp : Topology.IsEmbedding
      (fun p : L × IntegralLatticeGroup n => (p.1, integerVectorHom n p.2)) :=
    Topology.IsEmbedding.id.prodMap (integerVectorHom_isEmbedding n)
  exact (semidirectProductHomeomorph φ).symm.isEmbedding.comp
    (hp.comp (semidirectProductHomeomorph ρ).isEmbedding)

include hφ

theorem integralSemidirectEmbedding_compact_cover :
    ∃ K : Set (L ⋊[φ] Multiplicative (Fin n → ℝ)), IsCompact K ∧
      ∀ g, ∃ (a : L ⋊[ρ] IntegralLatticeGroup n)
        (k : L ⋊[φ] Multiplicative (Fin n → ℝ)), k ∈ K ∧
        integralSemidirectEmbedding ρ φ hφ a * k = g := by
  obtain ⟨F, hF, hcover⟩ := (integerVectorHom_uniform n).2
  let e := semidirectProductHomeomorph φ
  refine ⟨e.symm '' ({1} ×ˢ F), (isCompact_singleton.prod hF).image e.symm.continuous, ?_⟩
  intro g
  obtain ⟨z, v, hv, hz⟩ := hcover g.right
  obtain ⟨w, hw⟩ := z.property
  refine ⟨⟨g.left, w⟩, ⟨1, v⟩, ⟨(1, v), ⟨rfl, hv⟩, rfl⟩, ?_⟩
  apply SemidirectProduct.ext
  · change g.left * φ (integerVectorHom n w) 1 = g.left
    rw [map_one, mul_one]
  · change integerVectorHom n w * v = g.right
    rw [hw]
    exact hz

/-- The image of any uniform lattice remains uniform in the real extension. -/
theorem uniformLattice_integralSemidirect_image
    [IsTopologicalGroup L]
    (hcont : Continuous (fun p : Multiplicative (Fin n → ℝ) × L => φ p.1 p.2))
    {Γ : Subgroup (L ⋊[ρ] IntegralLatticeGroup n)} (hΓ : IsUniformLattice Γ) :
    IsUniformLattice (Γ.map (integralSemidirectEmbedding ρ φ hφ)) := by
  let := semidirectProductTopologicalGroup φ hcont
  obtain ⟨K, hK, hcover⟩ := integralSemidirectEmbedding_compact_cover ρ φ hφ
  exact hΓ.map_of_compact_cover _ (integralSemidirectEmbedding_isEmbedding ρ φ hφ) K hK hcover

end PolycyclicRecognition

end

end OAI
