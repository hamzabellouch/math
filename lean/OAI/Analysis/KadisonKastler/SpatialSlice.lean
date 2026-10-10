import OAI.Analysis.KadisonKastler.SpatialProduct

namespace OAI

/-! # Concrete vector slices of the spatial von Neumann product -/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem spatialLeft_tensorVector (ξ : K) (a : H →L[ℂ] H) :
    (spatialLeft a) ∘L tensorVector ξ = tensorVector ξ ∘L a := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, tensorVector_apply]
  exact spatialTensorOp_coe a 1 (x ⊗ₜ[ℂ] ξ)

theorem tensorVector_adjoint_spatialLeft (ξ : K) (a : H →L[ℂ] H) :
    (tensorVector ξ).adjoint ∘L spatialLeft a = a ∘L (tensorVector ξ).adjoint := by
  have he := congrArg (fun L : H →L[ℂ] SpatialHilbert H K => L.adjoint)
    (spatialLeft_tensorVector ξ (star a))
  have hs : (spatialLeft (H := H) (K := K) (star a)).adjoint =
      spatialLeft (H := H) (K := K) a := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
  have ha : (star a).adjoint = a := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_star]
  simpa only [ContinuousLinearMap.adjoint_comp, hs, ha] using he

/-- A first-leg commutant element commutes with the entire actual product. -/
theorem spatialLeft_commutes_product (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (a : H →L[ℂ] H) (ha : a ∈ M.commutant)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (hT : T ∈ spatialProductAlgebra M D) :
    spatialLeft a * T = T * spatialLeft a := by
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
      (D.toStarSubalgebra.map (spatialRight (H := H) (K := K)))
  have hB : B ≤ StarSubalgebra.centralizer ℂ {spatialLeft (K := K) a} := by
    apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hg' : g = spatialLeft (K := K) a := Set.mem_singleton_iff.mp hg
      subst g
      constructor
      · change spatialLeft (K := K) a * spatialLeft (K := K) x =
          spatialLeft (K := K) x * spatialLeft (K := K) a
        simpa only [map_mul] using (congrArg (spatialLeft (K := K))
          (VonNeumannAlgebra.mem_commutant_iff.mp ha x hx)).symm
      · change star (spatialLeft (K := K) a) * spatialLeft (K := K) x =
          spatialLeft (K := K) x * star (spatialLeft (K := K) a)
        rw [← map_star]
        have hs := VonNeumannAlgebra.mem_commutant_iff.mp
          (M.commutant.toStarSubalgebra.star_mem' ha) x hx
        simpa only [map_mul] using (congrArg (spatialLeft (K := K)) hs).symm
    · rintro _ ⟨x, hx, rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hg' : g = spatialLeft (K := K) a := Set.mem_singleton_iff.mp hg
      subst g
      constructor
      · exact (Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
          (StarAlgHom.id ℂ (K →L[ℂ] K)) a x).eq
      · rw [← map_star]
        exact (Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
          (StarAlgHom.id ℂ (K →L[ℂ] K)) (star a) x).eq
  have hLa : spatialLeft (K := K) a ∈ Set.centralizer (B : Set _) := by
    intro x hx
    have hx' := hB hx
    rw [StarSubalgebra.mem_centralizer_iff] at hx'
    exact (hx' _ (Set.mem_singleton _)).1.symm
  change T ∈ generatedVonNeumannAlgebra B at hT
  change T ∈ (generatedVonNeumannAlgebra B : Set _) at hT
  rw [generatedVonNeumannAlgebra_coe] at hT
  exact hT _ hLa

/-- Slicing an element of the spatial product lands in the original
first algebra, by the bicommutant theorem. -/
theorem tensorVectorSlice_mem (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (ξ : K) (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D) : tensorVectorSlice ξ T ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have hTcomm := spatialLeft_commutes_product M D a ha T hT
  have hV := spatialLeft_tensorVector ξ a
  have hVs := tensorVector_adjoint_spatialLeft ξ a
  apply ContinuousLinearMap.ext
  intro x
  have hVx := congrArg (fun L : H →L[ℂ] SpatialHilbert H K => L x) hV
  have hVsx := congrArg (fun L : SpatialHilbert H K →L[ℂ] H => L (T (tensorVector ξ x))) hVs
  have hc := congrArg (fun L : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    L (tensorVector ξ x)) hTcomm
  change a ((tensorVector ξ).adjoint (T (tensorVector ξ x))) =
    (tensorVector ξ).adjoint (T (tensorVector ξ (a x)))
  change (tensorVector ξ).adjoint (spatialLeft a (T (tensorVector ξ x))) =
    a ((tensorVector ξ).adjoint (T (tensorVector ξ x))) at hVsx
  change spatialLeft a (T (tensorVector ξ x)) = T (spatialLeft a (tensorVector ξ x)) at hc
  rw [← hVsx, hc]
  change spatialLeft a (tensorVector ξ x) = tensorVector ξ (a x) at hVx
  rw [hVx]

end

end KadisonKastler

end OAI
