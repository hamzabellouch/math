import OAI.Analysis.KadisonKastler.SpatialAssociator
import OAI.Analysis.KadisonKastler.CanonicalAmplification

namespace OAI

/-! # Tensoring Hilbert-space identifications

An isometric equivalence in either Hilbert tensor leg lifts to the
completed tensor product. Conjugation by this equivalence transports
both the bounded tensor operators and their generated spatial algebras.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct

noncomputable section

variable {H K H' K' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

/-- The completed tensor product of two Hilbert-space identifications. -/
def spatialTensorEquiv (f : H ≃ₗᵢ[ℂ] H') (g : K ≃ₗᵢ[ℂ] K') :
    SpatialHilbert H K ≃ₗᵢ[ℂ] SpatialHilbert H' K' :=
  (TensorProduct.congrIsometry f g).toLinearEquiv.extendOfIsometry
    UniformSpace.Completion.toComplₗᵢ.toLinearMap
    UniformSpace.Completion.toComplₗᵢ.toLinearMap
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (fun x => by
      change ‖((TensorProduct.congrIsometry f g x : H' ⊗[ℂ] K') : SpatialHilbert H' K')‖ =
        ‖(x : SpatialHilbert H K)‖
      simp only [UniformSpace.Completion.norm_coe, LinearIsometryEquiv.norm_map])

@[simp]
theorem spatialTensorEquiv_coe (f : H ≃ₗᵢ[ℂ] H') (g : K ≃ₗᵢ[ℂ] K')
    (x : H ⊗[ℂ] K) :
    spatialTensorEquiv f g (x : SpatialHilbert H K) =
      ((TensorProduct.congrIsometry f g x : H' ⊗[ℂ] K') : SpatialHilbert H' K') :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

@[simp]
theorem spatialTensorEquiv_tmul (f : H ≃ₗᵢ[ℂ] H') (g : K ≃ₗᵢ[ℂ] K') (x : H) (y : K) :
    spatialTensorEquiv f g ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      ((f x ⊗ₜ[ℂ] g y : H' ⊗[ℂ] K') : SpatialHilbert H' K') := by
  rw [spatialTensorEquiv_coe]
  rfl

@[simp]
theorem spatialTensorEquiv_symm_tmul
    (f : H ≃ₗᵢ[ℂ] H') (g : K ≃ₗᵢ[ℂ] K') (x : H') (y : K') :
    (spatialTensorEquiv f g).symm ((x ⊗ₜ[ℂ] y : H' ⊗[ℂ] K') : SpatialHilbert H' K') =
      ((f.symm x ⊗ₜ[ℂ] g.symm y : H ⊗[ℂ] K) : SpatialHilbert H K) := by
  apply (spatialTensorEquiv f g).injective
  rw [LinearIsometryEquiv.apply_symm_apply, spatialTensorEquiv_tmul,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

variable [CompleteSpace H] [CompleteSpace K] [CompleteSpace H'] [CompleteSpace K']

/-- Tensor-product operators transform componentwise. -/
theorem spatialTensorEquiv_conjugate_tensor
    (f : H ≃ₗᵢ[ℂ] H') (g : K ≃ₗᵢ[ℂ] K') (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    (spatialTensorEquiv f g).conjStarAlgEquiv (spatialTensorOp a b) =
      spatialTensorOp (f.conjStarAlgEquiv a) (g.conjStarAlgEquiv b) := by
  apply spatialTensorOp_ext
  intro x y
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    spatialTensorEquiv_symm_tmul, spatialTensorOp_coe, TensorProduct.mapL_tmul,
    spatialTensorEquiv_tmul]

/-- Transport commutes with taking the generated concrete von Neumann algebra. -/
theorem spatialTransport_generated
    (f : H ≃ₗᵢ[ℂ] H') (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    spatialTransportAlgebra f (generatedVonNeumannAlgebra S) =
      generatedVonNeumannAlgebra (S.map f.conjStarAlgEquiv.toStarAlgHom) := by
  apply SetLike.coe_injective
  change f.conjStarAlgEquiv '' (generatedVonNeumannAlgebra S : Set (H →L[ℂ] H)) =
    (generatedVonNeumannAlgebra (S.map f.conjStarAlgEquiv.toStarAlgHom) :
      Set (H' →L[ℂ] H'))
  rw [generatedVonNeumannAlgebra_coe, generatedVonNeumannAlgebra_coe]
  change f.conjStarAlgEquiv '' Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) =
    Set.centralizer (Set.centralizer (f.conjStarAlgEquiv '' (S : Set (H →L[ℂ] H))))
  rw [centralizer_image_spatial, centralizer_image_spatial]

/-- Tensoring Hilbert-space identifications transports both spatial factors. -/
theorem spatialTensorEquiv_spatialProduct
    (f : H ≃ₗᵢ[ℂ] H') (g : K ≃ₗᵢ[ℂ] K')
    (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    spatialTransportAlgebra (spatialTensorEquiv f g) (spatialProductAlgebra M D) =
      spatialProductAlgebra (spatialTransportAlgebra f M) (spatialTransportAlgebra g D) := by
  have hleft : (spatialTensorEquiv f g).conjStarAlgEquiv.toStarAlgHom.comp
      (spatialLeft (H := H) (K := K)) =
      (spatialLeft (H := H') (K := K')).comp f.conjStarAlgEquiv.toStarAlgHom := by
    apply StarAlgHom.ext
    intro a
    change (spatialTensorEquiv f g).conjStarAlgEquiv (spatialTensorOp a 1) =
      spatialTensorOp (f.conjStarAlgEquiv a) 1
    simpa only [map_one] using spatialTensorEquiv_conjugate_tensor f g a 1
  have hright : (spatialTensorEquiv f g).conjStarAlgEquiv.toStarAlgHom.comp
      (spatialRight (H := H) (K := K)) =
      (spatialRight (H := H') (K := K')).comp g.conjStarAlgEquiv.toStarAlgHom := by
    apply StarAlgHom.ext
    intro b
    change (spatialTensorEquiv f g).conjStarAlgEquiv (spatialTensorOp 1 b) =
      spatialTensorOp 1 (g.conjStarAlgEquiv b)
    simpa only [map_one] using spatialTensorEquiv_conjugate_tensor f g 1 b
  unfold spatialProductAlgebra
  rw [spatialTransport_generated]
  congr 1
  change (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K)) ⊔
      D.toStarSubalgebra.map (spatialRight (H := H) (K := K))).map
        (spatialTensorEquiv f g).conjStarAlgEquiv.toStarAlgHom =
    (M.toStarSubalgebra.map f.conjStarAlgEquiv.toStarAlgHom).map
        (spatialLeft (H := H') (K := K')) ⊔
      (D.toStarSubalgebra.map g.conjStarAlgEquiv.toStarAlgHom).map
        (spatialRight (H := H') (K := K'))
  rw [StarSubalgebra.map_sup]
  simp only [StarSubalgebra.map_map, hleft, hright]

/-- Changing only the second tensor leg preserves the first algebra. -/
theorem spatialTensorEquiv_right_spatialProduct
    (g : K ≃ₗᵢ[ℂ] K') (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    spatialTransportAlgebra (spatialTensorEquiv (LinearIsometryEquiv.refl ℂ H) g)
      (spatialProductAlgebra M D) =
        spatialProductAlgebra M (spatialTransportAlgebra g D) := by
  have h := spatialTensorEquiv_spatialProduct (LinearIsometryEquiv.refl ℂ H) g M D
  have hrefl : spatialTransportAlgebra (LinearIsometryEquiv.refl ℂ H) M = M := by
    apply SetLike.coe_injective
    ext a
    change a ∈ spatialTransportAlgebra (LinearIsometryEquiv.refl ℂ H) M ↔ a ∈ M
    rw [mem_spatialTransportAlgebra]
    rfl
  simpa only [hrefl] using h

end

end KadisonKastler

end OAI
