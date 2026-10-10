import OAI.Analysis.Nuclearity.MinimalFactorExtension
import OAI.Analysis.Nuclearity.RepresentedFactorTensor
import OAI.Analysis.Nuclearity.RepresentedImageData
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorLaws

namespace OAI

/-! The factor-image kernel formula in Tomiyama's Theorem 5. Nuclearity
of the actual represented left quotient remains an explicit input. -/

noncomputable section

namespace WeakPureInfiniteness

universe u v w
variable {A : Type u} {B : Type v} {H : Type w} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance representedKernelUnital : CStarAlgebra (MinimalTensor A B) :=
  minimalTensorUnitalStructure A B

abbrev UnitalTensorRepresentation := MinimalTensor A B →⋆ₐ[ℂ] (H →L[ℂ] H)

attribute [-instance] representedKernelUnital

def unitalTensorRepresentationNonunital
    (π : UnitalTensorRepresentation (A := A) (B := B) (H := H)) :
    MinimalTensor A B →⋆ₙₐ[ℂ] (H →L[ℂ] H) := by
  let _ : CStarAlgebra (MinimalTensor A B) := minimalTensorUnitalStructure A B
  exact π.toNonUnitalStarAlgHom

variable (π : UnitalTensorRepresentation (A := A) (B := B) (H := H))
  (F : RepresentedImageData (leftRepresentedMap π))
  (G : RepresentedImageData (rightRepresentedMap π))

def representedTensorQuotient : MinimalTensor A B →⋆ₙₐ[ℂ] MinimalTensor F.Carrier G.Carrier :=
  minimalMapAny F.quotient.toNonUnitalStarAlgHom G.quotient.toNonUnitalStarAlgHom

@[simp] theorem representedTensorQuotient_elementary (a : A) (b : B) :
    representedTensorQuotient π F G (minimalElementary a b) =
      minimalElementary (F.quotient a) (G.quotient b) :=
  minimalMapAny_elementary _ _ a b

theorem representedTensorQuotient_kernel
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ c : ℂ, T = c • 1)
    (hN : Pureness.IsNuclear.{w,w} F.Carrier) (x : MinimalTensor A B) :
    representedTensorQuotient π F G x = 0 ↔ π x = 0 := by
  let L := leftRepresentedMap π
  let R := rightRepresentedMap π
  let M := KirchbergRordam.GenericRW.GroupedFactors.bicommutant L.range
  have hLM (c : F.Carrier) : F.inclusion c ∈ M := by
    obtain ⟨a, rfl⟩ := F.surjective c
    rw [F.agrees]
    exact KirchbergRordam.GenericRW.GroupedFactors.subset_bicommutant L.range (L a) ⟨a, rfl⟩
  have hRM (d : G.Carrier) : G.inclusion d ∈ M.commutant := by
    obtain ⟨b, rfl⟩ := G.surjective d
    rw [G.agrees]
    exact minimalTensor_right_mem_left_commutant π b
  have hLR (c : F.Carrier) (d : G.Carrier) : Commute (F.inclusion c) (G.inclusion d) := by
    obtain ⟨a, rfl⟩ := F.surjective c
    obtain ⟨b, rfl⟩ := G.surjective d
    rw [F.agrees, G.agrees]
    exact (UnitalMinimalTensor.legs_commute A B a b).map π
  obtain ⟨θ, hθ, he⟩ := exists_minimal_factor_tensor_extension hN M
    (minimalTensor_left_factor π hs) F.inclusion G.inclusion F.injective G.injective hLM hRM hLR
  have heq : θ.comp (representedTensorQuotient π F G) = unitalTensorRepresentationNonunital π := by
    apply minimalTensor_hom_ext
    intro a b
    rw [NonUnitalStarAlgHom.comp_apply, representedTensorQuotient_elementary, he, F.agrees, G.agrees]
    change unitalTensorRepresentationNonunital π (UnitalMinimalTensor.leftEmbedding A B a) *
      unitalTensorRepresentationNonunital π (UnitalMinimalTensor.rightEmbedding A B b) = _
    rw [← map_mul, UnitalMinimalTensor.legs_mul]
  have hx : θ (representedTensorQuotient π F G x) = π x := congrArg (fun f => f x) heq
  constructor
  · intro h
    rw [← hx, h, map_zero]
  · intro h
    apply hθ.injective
    rw [map_zero, hx, h]

end WeakPureInfiniteness

end

end OAI
