import OAI.Analysis.KadisonKastler.SpatialSlice
import OAI.Analysis.KadisonKastler.ProductStateIrreducible
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace OAI

/-! # Right-leg slices and the relative commutant of a product centralizer -/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Insert a fixed vector in the first tensor leg. -/
def leftTensorVector (ξ : H) : K →L[ℂ] SpatialHilbert H K :=
  UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ H K ξ)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem leftTensorVector_apply (ξ : H) (η : K) :
    leftTensorVector ξ η = ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K) := rfl

/-- Compression in the first leg, with values in operators on the second. -/
def rightTensorSlice (ξ : H) :
    (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) →ₗ[ℂ] (K →L[ℂ] K) where
  toFun T := (leftTensorVector ξ).adjoint ∘L T ∘L leftTensorVector ξ
  map_add' S T := by ext η; simp
  map_smul' c T := by ext η; simp

omit [CompleteSpace H] in
@[simp]
theorem rightTensorSlice_apply (ξ : H)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (η : K) :
    rightTensorSlice ξ T η = (leftTensorVector ξ).adjoint (T (leftTensorVector ξ η)) := rfl

theorem spatialRight_leftTensorVector (ξ : H) (b : K →L[ℂ] K) :
    spatialRight b ∘L leftTensorVector ξ = leftTensorVector ξ ∘L b := by
  ext η
  simp only [ContinuousLinearMap.comp_apply, leftTensorVector_apply]
  exact spatialTensorOp_coe 1 b (ξ ⊗ₜ[ℂ] η)

theorem leftTensorVector_adjoint_spatialRight (ξ : H) (b : K →L[ℂ] K) :
    (leftTensorVector ξ).adjoint ∘L spatialRight b = b ∘L (leftTensorVector ξ).adjoint := by
  have he := congrArg (fun L : K →L[ℂ] SpatialHilbert H K => L.adjoint)
    (spatialRight_leftTensorVector ξ (star b))
  have hs : (spatialRight (H := H) (K := K) (star b)).adjoint =
      spatialRight (H := H) (K := K) b := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
  have hb : (star b).adjoint = b := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_star]
  simpa only [ContinuousLinearMap.adjoint_comp, hs, hb] using he

/-- A second-leg commutant element commutes with the entire spatial product. -/
theorem spatialRight_commutes_product (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (b : K →L[ℂ] K) (hb : b ∈ D.commutant)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (hT : T ∈ spatialProductAlgebra M D) :
    spatialRight b * T = T * spatialRight b := by
  let A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
      (D.toStarSubalgebra.map (spatialRight (H := H) (K := K)))
  have hA : A ≤ StarSubalgebra.centralizer ℂ {spatialRight (H := H) b} := by
    apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hg' : g = spatialRight (H := H) b := Set.mem_singleton_iff.mp hg
      subst g
      constructor
      · exact (Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
          (StarAlgHom.id ℂ (K →L[ℂ] K)) x b).eq.symm
      · rw [← map_star]
        exact (Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
          (StarAlgHom.id ℂ (K →L[ℂ] K)) x (star b)).eq.symm
    · rintro _ ⟨x, hx, rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hg' : g = spatialRight (H := H) b := Set.mem_singleton_iff.mp hg
      subst g
      constructor
      · change spatialRight (H := H) b * spatialRight (H := H) x =
          spatialRight (H := H) x * spatialRight (H := H) b
        simpa only [map_mul] using (congrArg (spatialRight (H := H))
          (VonNeumannAlgebra.mem_commutant_iff.mp hb x hx)).symm
      · change star (spatialRight (H := H) b) * spatialRight (H := H) x =
          spatialRight (H := H) x * star (spatialRight (H := H) b)
        rw [← map_star]
        have hs := VonNeumannAlgebra.mem_commutant_iff.mp
          (D.commutant.toStarSubalgebra.star_mem' hb) x hx
        simpa only [map_mul] using (congrArg (spatialRight (H := H)) hs).symm
  have hRb : spatialRight (H := H) b ∈ Set.centralizer (A : Set _) := by
    intro x hx
    have hx' := hA hx
    rw [StarSubalgebra.mem_centralizer_iff] at hx'
    exact (hx' _ (Set.mem_singleton _)).1.symm
  change T ∈ generatedVonNeumannAlgebra A at hT
  change T ∈ (generatedVonNeumannAlgebra A : Set _) at hT
  rw [generatedVonNeumannAlgebra_coe] at hT
  exact hT _ hRb

/-- Right-leg compression intertwines any second-leg operator commuting
with the operator being compressed. -/
theorem rightTensorSlice_commute (ξ : H)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (b : K →L[ℂ] K)
    (hc : spatialRight b * T = T * spatialRight b) :
    b * rightTensorSlice ξ T = rightTensorSlice ξ T * b := by
  have hV := spatialRight_leftTensorVector ξ b
  have hVs := leftTensorVector_adjoint_spatialRight ξ b
  ext η
  have hVη := congrArg (fun L : K →L[ℂ] SpatialHilbert H K => L η) hV
  have hVsη := congrArg (fun L : SpatialHilbert H K →L[ℂ] K =>
    L (T (leftTensorVector ξ η))) hVs
  have hcη := congrArg (fun L : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    L (leftTensorVector ξ η)) hc
  change b ((leftTensorVector ξ).adjoint (T (leftTensorVector ξ η))) =
    (leftTensorVector ξ).adjoint (T (leftTensorVector ξ (b η)))
  change (leftTensorVector ξ).adjoint (spatialRight b (T (leftTensorVector ξ η))) =
    b ((leftTensorVector ξ).adjoint (T (leftTensorVector ξ η))) at hVsη
  change spatialRight b (T (leftTensorVector ξ η)) =
    T (spatialRight b (leftTensorVector ξ η)) at hcη
  rw [← hVsη, hcη]
  change spatialRight b (leftTensorVector ξ η) = leftTensorVector ξ (b η) at hVη
  rw [hVη]

/-- Slicing the actual spatial product lands in its second algebra. -/
theorem rightTensorSlice_mem (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (ξ : H) (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D) : rightTensorSlice ξ T ∈ D := by
  rw [← D.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  exact rightTensorSlice_commute ξ T b (spatialRight_commutes_product M D b hb T hT)

/-- Irreducibility of the product-state centralizer scalarizes every
right-leg compression of an operator in its spatial relative commutant. -/
theorem rightTensorSlice_scalar_of_local_swaps
    (M : VonNeumannAlgebra H) {D : VonNeumannAlgebra K} {Ω : K}
    (L : LocalProductSwaps D Ω) (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D)
    (hcomm : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → spatialRight (u : K →L[ℂ] K) * T =
        T * spatialRight (u : K →L[ℂ] K)) (ξ : H) :
    ∃ z : ℂ, rightTensorSlice ξ T = z • (1 : K →L[ℂ] K) := by
  refine ⟨productVectorState Ω (rightTensorSlice ξ T),
    L.scalar_of_commutes hΩ hsep _ (rightTensorSlice_mem M D ξ T hT) ?_⟩
  intro u hu hc
  exact rightTensorSlice_commute ξ T u (hcomm u hu hc)

end

end KadisonKastler

end OAI
