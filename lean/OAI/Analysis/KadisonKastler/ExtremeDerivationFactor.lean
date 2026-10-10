import OAI.Analysis.KadisonKastler.ExtremeSignedProjection
import OAI.Analysis.KadisonKastler.DerivationExtensionFactor

namespace OAI

/-! # The factor lemma for an extreme derivation separator

This is the unital application of the factor lemma on p.261 of Sakai's
1971 paper. The signed cyclic representation is constructed separately;
central projections commute with the spatial derivation implementer,
so extremality forces them to be trivial.
-/

namespace KadisonKastler

noncomputable section

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem factor_of_extreme_signed_derivation_extension
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hgen : NormGeneratedExtension φ d)
    (D : A →L[ℂ] A) (hd : ∀ a, φ (D a) = d * φ a - φ a * d)
    (F : WeakDual ℂ B) (hF : F ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcyc : DenseRange (fun b => π b ξ))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSS : S * S = 1)
    (hSπ : ∀ b, Commute S (π b)) (hrep : F.toStrongDual = signedVectorFunctional π S ξ) :
    ScalarCenter (generatedVonNeumannAlgebra (π.comp φ).range) := by
  let N := generatedVonNeumannAlgebra (π.comp φ).range
  have hcomm : ∀ a : (π.comp φ).range,
      π d * a.val - a.val * π d ∈ N := by
    intro a
    obtain ⟨x, hx⟩ := a.property
    change π (φ x) = a.val at hx
    rw [← hx, ← map_mul, ← map_mul, ← map_sub, ← hd]
    exact subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨D x, rfl⟩
  have hproj : ∀ q : Algebra N, IsStarProjection q →
      (∀ a : Algebra N, a * q = q * a) → q = 0 ∨ q = 1 := by
    intro q hq hqc
    have hp : IsStarProjection q.val := hq.map N.toStarSubalgebra.subtype
    have hqp : ∀ a ∈ N, Commute q.val a := by
      intro a ha
      exact (congrArg Subtype.val (hqc ⟨a, ha⟩)).symm
    have hqd := (spatial_commutator_central_projection
      (π.comp φ).range (π d) hcomm q.val hp q.property hqp).symm
    have hqA : ∀ a, Commute q.val (π (φ a)) := by
      intro a
      exact hqp _ (subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨a, rfl⟩)
    have hqB : ∀ b, Commute q.val (π b) :=
      commutes_of_normGeneratedExtension φ d hgen π q.val hp.isSelfAdjoint hqA hqd
    have hSin : S ∈ Set.centralizer ((π.comp φ).range : Set (H →L[ℂ] H)) := by
      rintro a ⟨b, hb⟩
      change π (φ b) = a at hb
      rw [← hb]
      exact (hSπ (φ b)).eq.symm
    have hqin : q.val ∈ Set.centralizer
        (Set.centralizer ((π.comp φ).range : Set (H →L[ℂ] H))) := by
      rw [← generatedVonNeumannAlgebra_coe]
      exact q.property
    have hqS : Commute q.val S := (hqin S hSin).symm
    exact (extreme_signed_projection_trivial φ F hF π ξ hξ hcyc S hS hSS hSπ hrep
      q.val hp hqB hqS q.property).imp Subtype.ext Subtype.ext
  intro T hTN hTc
  obtain ⟨z, hz⟩ := scalar_center_of_trivial_central_projections N hproj
    ⟨T, hTN⟩ (fun a => Subtype.ext (hTc a.val a.property))
  exact ⟨z, congrArg Subtype.val hz⟩

end

end KadisonKastler

end OAI
