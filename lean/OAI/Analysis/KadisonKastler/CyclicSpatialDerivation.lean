import OAI.Analysis.KadisonSimilarity.Derivation.CyclicColumnTests
import OAI.Analysis.KadisonSimilarity.Similarity.PaulsenDischarge
import OAI.Analysis.KadisonKastler.SimpleIrreducibleRepresentation

namespace OAI

/-! # Spatial implementation in the initial irreducible representation

The proved cyclic column estimate and completely bounded factorization
implement a bounded derivation in a cyclic representation. Taking the real
part gives the self-adjoint implementer used in Sakai's quotient argument.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cyclic_spatial_derivation
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hcyclic : ∃ ξ : H, DenseRange (fun a : A => π a ξ))
    (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∃ T : H →L[ℂ] H, ∀ a, π (D a) = T * π a - π a * T := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let δ : A →L[ℂ] (H →L[ℂ] H) :=
    { toLinearMap := π.toLinearMap.comp D.toLinearMap
      cont := by
        change Continuous (fun a => π (D a))
        exact (show Continuous π by fun_prop).comp D.continuous }
  have hδ : ∀ a b, δ (a * b) = (π a).comp (δ b) + (δ a).comp (π b) := by
    intro a b
    change π (D (a * b)) = π a * π (D b) + π (D a) * π b
    rw [hD, map_add, map_mul, map_mul, add_comm]
  obtain ⟨ξ, hξ⟩ := hcyclic
  obtain ⟨T, hT, _⟩ := KadisonSimilarity.cyclic_derivation_implementation_of_column_tests
    π π δ hδ (KadisonSimilarity.cyclicColumnTests_of_dense_orbit π ξ hξ)
    (KadisonSimilarity.paulsenSimilarityInput
      (KadisonSimilarity.normalizedRectangularRepresentation π π δ hδ))
  exact ⟨T, hT⟩

theorem selfAdjoint_spatial_implementer
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : A →L[ℂ] A)
    (hstar : ∀ a, D (star a) = -star (D a))
    (T : H →L[ℂ] H) (hT : ∀ a, π (D a) = T * π a - π a * T) :
    ∃ S : H →L[ℂ] H, IsSelfAdjoint S ∧
      ∀ a, π (D a) = S * π a - π a * S := by
  have hTs : ∀ a, π (D a) = star T * π a - π a * star T := by
    intro a
    have h := congrArg star (hT (star a))
    rw [hstar, map_neg, map_star, star_neg, star_star,
      star_sub, star_mul, star_mul, map_star, star_star] at h
    exact neg_injective (by simpa only [neg_sub] using h)
  refine ⟨(1 / 2 : ℂ) • (T + star T),
    (show IsSelfAdjoint (1 / 2 : ℂ) by norm_num [isSelfAdjoint_iff]).smul
      (IsSelfAdjoint.add_star_self T), ?_⟩
  intro a
  calc
    π (D a) = (1 / 2 : ℂ) • (π (D a) + π (D a)) := by
      rw [← two_smul ℂ (π (D a)), smul_smul]
      norm_num
    _ = (1 / 2 : ℂ) • ((T * π a - π a * T) +
        (star T * π a - π a * star T)) := by
      conv_lhs => arg 2; arg 1; rw [hT]
      conv_lhs => arg 2; arg 2; rw [hTs]
    _ = ((1 / 2 : ℂ) • (T + star T)) * π a -
        π a * ((1 / 2 : ℂ) • (T + star T)) := by
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_sub, smul_add]
      abel

theorem exists_simple_spatial_derivation [Nontrivial A]
    (hA : CStarSimple A) (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : Nontrivial H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective π ∧ NaimarkZFC.IsIrreducible π.toNonUnitalStarAlgHom ∧
      ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧
        ∀ a, π (D a) = T * π a - π a * T := by
  obtain ⟨H, _, _, _, _, π, hπ, hirr, ξ, _, hξ⟩ :=
    exists_simple_irreducible_representation hA
  obtain ⟨T, hT⟩ := cyclic_spatial_derivation π ⟨ξ, hξ⟩ D hD
  obtain ⟨S, hS, hSD⟩ := selfAdjoint_spatial_implementer π D hstar T hT
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, π,
    hπ, hirr, S, hS, hSD⟩

end

end KadisonKastler

end OAI
