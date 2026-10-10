import OAI.Analysis.OperatorAlgebra.DensityRootTrace

namespace OAI

/-! Passing the density-root trace identity through a common finite
support, without finite-dimensionality of the represented Hilbert space. -/

noncomputable section
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

variable {H E F K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma tensorIsometry_compression (f : F →ₗᵢ[ℂ] H) (g : K →ₗᵢ[ℂ] E)
    (A : H →L[ℂ] H) (B : E →L[ℂ] E) (z w : F ⊗[ℂ] K) :
    inner ℂ (TensorProduct.mapIsometry f g z)
      (TensorProduct.mapL A B (TensorProduct.mapIsometry f g w)) =
    inner ℂ z (TensorProduct.mapL
      (f.toContinuousLinearMap.adjoint ∘L A ∘L f.toContinuousLinearMap)
      (g.toContinuousLinearMap.adjoint ∘L B ∘L g.toContinuousLinearMap) w) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      induction w using TensorProduct.inductionOn with
      | tmul v t =>
          simp only [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
            TensorProduct.mapL_tmul, TensorProduct.inner_tmul]
          change inner ℂ (f x) (A (f v)) * inner ℂ (g y) (B (g t)) =
            inner ℂ x (f.toContinuousLinearMap.adjoint (A (f v))) *
              inner ℂ y (g.toContinuousLinearMap.adjoint (B (g t)))
          rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
          rfl
      | add w₁ w₂ h₁ h₂ =>
          simpa only [map_add, inner_add_right (𝕜 := ℂ)] using congrArg₂ (· + ·) h₁ h₂
  | add z₁ z₂ h₁ h₂ =>
      simpa only [map_add, inner_add_left (𝕜 := ℂ)] using congrArg₂ (· + ·) h₁ h₂

lemma finiteTensorDensity_compression (f : F →ₗᵢ[ℂ] H) (z : E ⊗[ℂ] F)
    (A : H →L[ℂ] H) :
    (finiteTensorDensity (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) f z)).val A =
      (finiteTensorDensity z).val (f.toContinuousLinearMap.adjoint ∘L A ∘L f.toContinuousLinearMap) := by
  rw [finiteTensorDensity_apply, finiteTensorDensity_apply]
  have h := tensorIsometry_compression (LinearIsometry.id : E →ₗᵢ[ℂ] E) f
    (ContinuousLinearMap.id ℂ E) A z z
  have hi : (LinearIsometry.id : E →ₗᵢ[ℂ] E).toContinuousLinearMap.adjoint ∘L
      (ContinuousLinearMap.id ℂ E) ∘L (LinearIsometry.id : E →ₗᵢ[ℂ] E).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ E := by
    change (ContinuousLinearMap.id ℂ E).adjoint ∘L (ContinuousLinearMap.id ℂ E) ∘L
      (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ E
    rw [ContinuousLinearMap.adjoint_id]
    simp only [ContinuousLinearMap.comp_id]
  rw [hi] at h
  exact h

theorem densityRoot_left_quadratic (z : E ⊗[ℂ] H) (A : H →L[ℂ] H) :
    inner ℂ (NuclearUltrapower.densityRoot z)
      (densityLeftRepresentation A (NuclearUltrapower.densityRoot z)) =
        (finiteTensorDensity z).val A := by
  obtain ⟨F, hF, hFz⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({z} : Set (E ⊗[ℂ] H)) (Set.finite_singleton z)
  let : FiniteDimensional ℂ F := hF
  let : CompleteSpace F := FiniteDimensional.complete ℂ F
  let : InnerProductSpace ℂ (StrongDual ℂ F) := NuclearUltrapower.strongDualInner
  let : NormedAddCommGroup (F ⊗[ℂ] StrongDual ℂ F) :=
    TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := F) (F := StrongDual ℂ F)
  let : InnerProductSpace ℂ (F ⊗[ℂ] StrongDual ℂ F) :=
    TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := F) (F := StrongDual ℂ F)
  obtain ⟨w, hw⟩ := hFz (Set.mem_singleton z)
  have hm : TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) F.subtypeₗᵢ w = z := hw
  rw [← hm]
  simp only [NuclearUltrapower.densityRoot_mapIsometry, densityLeft_coe,
    UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := H ⊗[ℂ] StrongDual ℂ H)]
  let f := F.subtypeₗᵢ
  let g := NuclearUltrapower.dualIsometry f
  let t := NuclearUltrapower.finiteOperatorTensor (CFC.sqrt (NuclearUltrapower.reducedDensity w))
  change inner ℂ (TensorProduct.mapIsometry f g t)
    (TensorProduct.mapL A (ContinuousLinearMap.id ℂ (StrongDual ℂ H))
      (TensorProduct.mapIsometry f g t)) = _
  rw [tensorIsometry_compression]
  have hg : g.toContinuousLinearMap.adjoint ∘L (ContinuousLinearMap.id ℂ (StrongDual ℂ H)) ∘L
      g.toContinuousLinearMap = ContinuousLinearMap.id ℂ (StrongDual ℂ F) := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun T : StrongDual ℂ F →L[ℂ] StrongDual ℂ F => T x)
      g.adjoint_comp_self
    exact hx
  rw [hg]
  have ht := densityRoot_left_quadratic_finite w
    (f.toContinuousLinearMap.adjoint ∘L A ∘L f.toContinuousLinearMap)
  simp only [densityRoot_eq_finiteOperatorTensor, densityLeft_coe,
    UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := F ⊗[ℂ] StrongDual ℂ F)] at ht
  rw [ht]
  exact (finiteTensorDensity_compression f w A).symm

end WeakPureInfiniteness

end

end OAI
