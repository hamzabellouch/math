import OAI.Analysis.Nuclearity.UnitalMinimalTensor
import OAI.Analysis.Nuclearity.FactorTensorInjection
import OAI.Analysis.PureInfiniteness.InnerHomCompression

namespace OAI

/-! The factor restrictions of an irreducible representation of the minimal
tensor product. Neither factor algebra is assumed simple. -/

noncomputable section
open KirchbergRordam.GenericRW

namespace WeakPureInfiniteness

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance factorTensorUnital : CStarAlgebra (MinimalTensor A B) := minimalTensorUnitalStructure A B

theorem minimalTensor_commute_of_legs (π : MinimalTensor A B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H)
    (hL : ∀ a, Commute T (π (UnitalMinimalTensor.leftEmbedding A B a)))
    (hR : ∀ b, Commute T (π (UnitalMinimalTensor.rightEmbedding A B b))) :
    ∀ x, Commute T (π x) := by
  let S : Submodule ℂ (MinimalTensor A B) :=
    { carrier := {x | Commute T (π x)}
      zero_mem' := by change Commute T (π 0); rw [map_zero]; exact Commute.zero_right _
      add_mem' := fun {x y} hx hy => by
        change Commute T (π (x + y))
        rw [map_add]
        exact hx.add_right hy
      smul_mem' := fun c x hx => by
        change Commute T (π (c • x))
        rw [map_smul]
        exact hx.smul_right c }
  have hc : Continuous π := (starHomContinuousLinear π.toNonUnitalStarAlgHom).continuous
  have hs : S = ⊤ := by
    apply minimal_elementary_span_dense S
      (isClosed_eq (continuous_const.mul hc) (hc.mul continuous_const))
    intro a b
    change Commute T (π (minimalElementary a b))
    rw [← UnitalMinimalTensor.legs_mul, map_mul]
    exact (hL a).mul_right (hR b)
  intro x
  have hx : x ∈ S := by rw [hs]; trivial
  exact hx

theorem minimalTensor_left_factor (π : MinimalTensor A B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    FactorIndependence.IsFactor
      (GroupedFactors.bicommutant (π.comp (UnitalMinimalTensor.leftEmbedding A B)).range) := by
  apply GroupedFactors.isFactor_of_total _
    (π.comp (UnitalMinimalTensor.rightEmbedding A B)).range
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    exact (UnitalMinimalTensor.legs_commute A B a b).map π
  · intro T hL hR
    exact hs T (minimalTensor_commute_of_legs π T
      (fun a => hL _ ⟨a, rfl⟩) (fun b => hR _ ⟨b, rfl⟩))

theorem minimalTensor_right_mem_left_commutant
    (π : MinimalTensor A B →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : B) :
    π (UnitalMinimalTensor.rightEmbedding A B b) ∈
      (GroupedFactors.bicommutant (π.comp (UnitalMinimalTensor.leftEmbedding A B)).range).commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have hb : π (UnitalMinimalTensor.rightEmbedding A B b) ∈
      GroupedFactors.commutantOf (π.comp (UnitalMinimalTensor.leftEmbedding A B)).range := by
    apply (GroupedFactors.mem_commutantOf_iff _ _).mpr
    rintro x ⟨a, rfl⟩
    exact (UnitalMinimalTensor.legs_commute A B a b).map π
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hT _ hb).symm

end WeakPureInfiniteness

end

end OAI
