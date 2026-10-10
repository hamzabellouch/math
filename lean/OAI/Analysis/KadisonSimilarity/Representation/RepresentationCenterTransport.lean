import OAI.Analysis.KadisonSimilarity.Tracial.MatrixVonNeumannRange
import OAI.Analysis.KadisonSimilarity.Representation.CentralDecomposition

namespace OAI

/-! # Scalar centers and exact representation conjugacy

An algebra equivalence between the ambient operator algebras transports
the represented bicommutants and their centers. In particular, identifying
two equal projection ranges does not change the factor-fiber criterion.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem representation_bicommutant_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) :
    θ T ∈ representationVonNeumannAlgebra ρ := by
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT ⊢
  intro Q hQ
  have hpre : θ.symm Q ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H)) := by
    rintro _ ⟨a, rfl⟩
    apply θ.injective
    change θ (σ a * θ.symm Q) = θ (θ.symm Q * σ a)
    simp only [map_mul]
    change θ (σ a) * θ (θ.symm Q) = θ (θ.symm Q) * θ (σ a)
    rw [θ.apply_symm_apply, hθ]
    exact hQ (ρ a) ⟨a, rfl⟩
  have h := congrArg θ (hT (θ.symm Q) hpre)
  simpa only [map_mul, θ.apply_symm_apply] using h

theorem representation_bicommutant_map_mem_iff
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a) (T : H →L[ℂ] H) :
    θ T ∈ representationVonNeumannAlgebra ρ ↔ T ∈ representationVonNeumannAlgebra σ := by
  constructor
  · intro hT
    have h := representation_bicommutant_map_mem θ.symm ρ σ
      (fun a => by rw [← hθ a, θ.symm_apply_apply]) (θ T) hT
    simpa only [θ.symm_apply_apply] using h
  · exact representation_bicommutant_map_mem θ σ ρ hθ T

theorem representation_commutant_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ (representationVonNeumannAlgebra σ).commutant) :
    θ T ∈ (representationVonNeumannAlgebra ρ).commutant := by
  apply (mem_representation_commutant_iff ρ (θ T)).mpr
  have ht := (mem_representation_commutant_iff σ T).mp hT
  rintro _ ⟨a, rfl⟩
  change ρ a * θ T = θ T * ρ a
  simpa only [map_mul, hθ] using congrArg θ (ht (σ a) ⟨a, rfl⟩)

theorem representation_center_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ vonNeumannCenter (representationVonNeumannAlgebra σ)) :
    θ T ∈ vonNeumannCenter (representationVonNeumannAlgebra ρ) :=
  ⟨representation_bicommutant_map_mem θ σ ρ hθ T hT.1,
    representation_commutant_map_mem θ σ ρ hθ T hT.2⟩

/-- The scalar-center condition used for factor fibers is unchanged by an
exact star-algebra conjugacy of the representations. -/
theorem scalar_center_of_representation_equiv
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (hρ : ∀ a : (representationVonNeumannAlgebra ρ).toStarSubalgebra,
      (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c) :
    ∀ a : (representationVonNeumannAlgebra σ).toStarSubalgebra,
      (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c := by
  intro a ha
  have haCenter : (a : H →L[ℂ] H) ∈
      vonNeumannCenter (representationVonNeumannAlgebra σ) := by
    refine ⟨a.property, VonNeumannAlgebra.mem_commutant_iff.mpr ?_⟩
    intro b hb
    exact (congrArg Subtype.val (ha ⟨b, hb⟩)).symm
  have hθCenter := representation_center_map_mem θ σ ρ hθ a haCenter
  let aρ : (representationVonNeumannAlgebra ρ).toStarSubalgebra := ⟨θ a, hθCenter.1⟩
  have hcomm : ∀ b, aρ * b = b * aρ := by
    intro b
    apply Subtype.ext
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hθCenter.2) b b.property).symm
  obtain ⟨c, hc⟩ := hρ aρ hcomm
  refine ⟨c, Subtype.ext ?_⟩
  apply θ.injective
  have hval := congrArg Subtype.val hc
  change θ (a : H →L[ℂ] H) = algebraMap ℂ (K →L[ℂ] K) c at hval
  change θ (a : H →L[ℂ] H) = θ (algebraMap ℂ (H →L[ℂ] H) c)
  simpa only [Algebra.algebraMap_eq_smul_one, map_smul, map_one] using hval

end KadisonSimilarity

end

end OAI
