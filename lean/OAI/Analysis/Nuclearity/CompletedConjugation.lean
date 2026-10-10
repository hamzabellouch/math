import OAI.Analysis.Nuclearity.RepresentedTensorFunctional
import OAI.Analysis.Nuclearity.TensorFunctionalConjugation
import OAI.Analysis.Nuclearity.TensorFixedElement

namespace OAI

/-! Conjugation on the completed tensor product. Cyclic approximation of
finitely many coefficient vectors produces a genuine inner compression,
with its implementer in the nonunital algebra. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

variable {B C D H I J : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C]
  [NonUnitalCStarAlgebra D] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I] [Fintype J]

local instance completedTensorOrder : PartialOrder (MinimalTensor B C) := CStarAlgebra.spectralOrder _
local instance completedTensorOrdered : StarOrderedRing (MinimalTensor B C) := CStarAlgebra.spectralOrderedRing _

omit [Fintype J] in
lemma tensorCoefficientFunctional_conjugation (hB : Nuclear B)
    (f : B →L[ℂ] (H →L[ℂ] H)) (hf : CompletelyPositive f)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ b c, Commute (f b) (η c))
    (ξ : H) (x : I → B) (y : I → C) (z : MinimalTensor B C) :
    tensorCoefficientFunctional f η x (fun i => η (y i) ξ) z =
      nuclearTensorFunctional hB f hf η hc ξ
        (star (∑ i, minimalElementary (x i) (y i)) * z *
          (∑ i, minimalElementary (x i) (y i))) := by
  let d := ∑ i, minimalElementary (x i) (y i)
  let Φ := nuclearTensorFunctional hB f hf η hc ξ
  let L : MinimalTensor B C →L[ℂ] ℂ :=
    (⟨Φ.toLinearMap, map_continuous Φ⟩ : MinimalTensor B C →L[ℂ] ℂ).comp
      (ContinuousLinearMap.mulLeftRight ℂ (MinimalTensor B C) (star d) d)
  have he : tensorCoefficientFunctional f η x (fun i => η (y i) ξ) = L := by
    apply minimalTensor_clm_ext
    intro b c
    rw [tensorCoefficientFunctional_elementary hB f hf η hc]
    change _ = nuclearTensorFunctional hB f hf η hc ξ
      (star (∑ i, minimalElementary (x i) (y i)) * minimalElementary b c *
        (∑ i, minimalElementary (x i) (y i)))
    exact (nuclearTensorFunctional_finite_conjugation_vectors hB f hf η hc ξ x y b c).symm
  exact DFunLike.congr_fun he z

omit [Fintype J] [PartialOrder B] [StarOrderedRing B] [PartialOrder D] [StarOrderedRing D] in
lemma representedCompression_eq (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (v : D) :
    representedMap π (innerHomCompression β v) = representedCompression β π v := by
  apply ContinuousLinearMap.ext
  intro b
  exact (representedCompression_apply β π v b).symm


omit [Fintype I] [Fintype J] in
lemma representedTensorFunctional_inner (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) (v : D) :
    representedTensorFunctional hB π (innerHomCompression β v)
      (innerHomCompression_cp β v) η hc ξ =
      compressedTensorFunctional hB β π η hc ξ v := by
  unfold representedTensorFunctional compressedTensorFunctional
  congr 1
  exact representedCompression_eq β π v

omit [Fintype J] in
lemma tensorCoefficientFunctional_inner_unitized (hB : Nuclear B)
    (β : B →⋆ₙₐ[ℂ] D) (π : Unitization ℂ D →⋆ₐ[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c))
    (ξ : H) (v : D) (a : I → Unitization ℂ D) (x : I → B) (z : MinimalTensor B C) :
    let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ D)
    let hρ := fun (d : D) (c : C) => hc (d : Unitization ℂ D) c
    tensorCoefficientFunctional (representedCompression β ρ v) η x (fun i => π (a i) ξ) z =
      compressedTensorFunctional hB β ρ η hρ ξ
        (∑ i, unitizedRightMul (β (x i) * v) (a i)) z := by
  dsimp only
  let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ D)
  let hρ : ∀ d c, Commute (ρ d) (η c) := fun d c => hc (d : Unitization ℂ D) c
  let w := ∑ i, unitizedRightMul (β (x i) * v) (a i)
  have hw (b : B) : innerHomCompression β w b =
      unitizedCoefficientEnlargement (innerHomCompression β v) a x b :=
    (unitizedCoefficientEnlargement_inner β a x v b).symm
  have he := tensorCoefficientFunctional_unitized hB π η hc ξ
    (innerHomCompression β v) (innerHomCompression β w)
    (innerHomCompression_cp β v) (innerHomCompression_cp β w) a x hw z
  rw [representedCompression_eq] at he
  have hΦ : representedTensorFunctional hB ρ (innerHomCompression β w)
      (innerHomCompression_cp β w) η hρ ξ =
      compressedTensorFunctional hB β ρ η hρ ξ w := by
    unfold representedTensorFunctional compressedTensorFunctional
    congr 1
    exact representedCompression_eq β ρ w
  exact he.trans (DFunLike.congr_fun hΦ z)

theorem completed_conjugation_inner_approximation (hB : Nuclear B)
    (β : B →⋆ₙₐ[ℂ] D) (π : Unitization ℂ D →⋆ₐ[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c))
    (ξ : H) (hcyc : DenseRange (fun a => π a ξ)) (v : D)
    (x : I → B) (y : I → C) (z : J → MinimalTensor B C) (ε : ℝ) (hε : 0 < ε) :
    let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ D)
    let hρ := fun (d : D) (c : C) => hc (d : Unitization ℂ D) c
    ∃ a : I → Unitization ℂ D,
      ‖(fun j => compressedTensorFunctional hB β ρ η hρ ξ v
          (star (∑ i, minimalElementary (x i) (y i)) * z j *
            (∑ i, minimalElementary (x i) (y i)))) -
        (fun j => compressedTensorFunctional hB β ρ η hρ ξ
          (∑ i, unitizedRightMul (β (x i) * v) (a i)) (z j))‖ < ε := by
  dsimp only
  let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ D)
  let hρ : ∀ d c, Commute (ρ d) (η c) := fun d c => hc (d : Unitization ℂ D) c
  obtain ⟨a, ha⟩ := finite_tensor_coefficient_approximation
    (representedCompression β ρ v) η x π ξ hcyc (fun i => η (y i) ξ) z ε hε
  refine ⟨a, ?_⟩
  have hleft (j : J) := tensorCoefficientFunctional_conjugation hB
    (representedCompression β ρ v) (representedCompression_cp β ρ v) η
    (representedCompression_commute β ρ η hρ v) ξ x y (z j)
  have hright (j : J) :
      tensorCoefficientFunctional (representedCompression β ρ v) η x (fun i => π (a i) ξ) (z j) =
        compressedTensorFunctional hB β ρ η hρ ξ
          (∑ i, unitizedRightMul (β (x i) * v) (a i)) (z j) :=
    tensorCoefficientFunctional_inner_unitized hB β π η hc ξ v a x (z j)
  simp only [hleft, hright] at ha
  exact ha

omit [Fintype I] [Fintype J] in
lemma starHomContinuous_completelyPositive (β : B →⋆ₙₐ[ℂ] D) :
    CompletelyPositive (starHomContinuousLinear β) := by
  intro n M hM
  exact map_nonneg (CStarMatrix.mapₙₐ β) hM

omit [Fintype I] [Fintype J] in
lemma representedTensorFunctional_hom (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) :
    representedTensorFunctional hB π (starHomContinuousLinear β)
      (starHomContinuous_completelyPositive β) η hc ξ =
      inclusionTensorFunctional hB β π η hc ξ := by
  let Φ := representedTensorFunctional hB π (starHomContinuousLinear β)
    (starHomContinuous_completelyPositive β) η hc ξ
  let Ψ := inclusionTensorFunctional hB β π η hc ξ
  have he : (⟨Φ.toLinearMap, map_continuous Φ⟩ : MinimalTensor B C →L[ℂ] ℂ) =
      (⟨Ψ.toLinearMap, map_continuous Ψ⟩ : MinimalTensor B C →L[ℂ] ℂ) := by
    apply minimalTensor_clm_ext
    intro b c
    change Φ (minimalElementary b c) = Ψ (minimalElementary b c)
    rw [representedTensorFunctional_elementary, inclusionTensorFunctional_elementary]
    rfl
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun he z


end WeakPureInfiniteness

end

end OAI
