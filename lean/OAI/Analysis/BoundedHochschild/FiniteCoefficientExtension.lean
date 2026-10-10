import OAI.Analysis.BoundedHochschild.FiniteCompressionExtension

namespace OAI

/-! Finite collections of Hilbert-space coefficients admit simultaneous
contractive completely positive extensions. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem exists_finite_coefficient_extension (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    (hφ1 : φ ⟨1, h1⟩ = 1)
    (hφ : ∀ n (X : operatorSystemMatrices S n),
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) (s : Finset H) :
    ∃ Ψ : CompletelyPositiveMap A (H →L[ℂ] H),
      (∀ a, ‖Ψ a‖ ≤ ‖a‖) ∧ ∀ (a : S) (ξ : H), ξ ∈ s → ∀ η ∈ s,
        inner ℂ η (Ψ (a : A) ξ) = inner ℂ η (φ a ξ) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_ne (0 : H)
  let t := insert ζ s
  let E := Submodule.span ℂ (t : Set H)
  let : FiniteDimensional ℂ E := FiniteDimensional.span_finset ℂ t
  let ζE : E := ⟨ζ, Submodule.subset_span (Finset.mem_insert_self ζ s)⟩
  let : Nontrivial E := ⟨⟨ζE, 0, fun h => hζ (congrArg Subtype.val h)⟩⟩
  let b := stdOrthonormalBasis ℂ E
  let V : EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) →ₗᵢ[ℂ] H :=
    E.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let i₀ : Fin (Module.finrank ℂ E) := ⟨0, Module.finrank_pos⟩
  obtain ⟨Ψ, hΨ, hcoeff⟩ := exists_finite_compression_extension S h1 hstar φ hφ1 i₀ V
    (hφ (Module.finrank ℂ E))
  refine ⟨Ψ, hΨ, fun a ξ hξ η hη => ?_⟩
  let ξE : E := ⟨ξ, Submodule.subset_span (Finset.mem_insert_of_mem hξ)⟩
  let ηE : E := ⟨η, Submodule.subset_span (Finset.mem_insert_of_mem hη)⟩
  have hξE : V (b.repr ξE) = ξ := by
    change ((b.repr.symm (b.repr ξE) : E) : H) = ξ
    rw [b.repr.symm_apply_apply]
  have hηE : V (b.repr ηE) = η := by
    change ((b.repr.symm (b.repr ηE) : E) : H) = η
    rw [b.repr.symm_apply_apply]
  simpa only [hξE, hηE] using hcoeff a (b.repr ξE) (b.repr ηE)

end BoundedHochschild.KadisonRingrose

end

end OAI
