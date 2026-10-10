import OAI.Analysis.Mahler.ReferencePoleFrame

namespace OAI

open Complex MeasureTheory Metric
open scoped BigOperators

namespace Mahler

lemma exists_unitary_referencePole {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1) :
    ∃ L : ComplexEuclidean (k+1) ≃ₗᵢ[ℂ] ComplexEuclidean (k+1), L (referencePole k) = x := by
  classical
  have hv : Orthonormal ℂ (({0} : Set (Fin (k+1))).domRestrict (fun _ => x)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by simpa using i.property.trans j.property.symm)
    simp [hij, Set.domRestrict, inner_self_eq_norm_sq_to_K, hx]
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [ComplexEuclidean])
  refine ⟨b.repr.symm, ?_⟩
  rw [referencePole, b.repr_symm_single]
  exact hb 0 (Set.mem_singleton 0)

lemma sphereVolume_unitary {k : ℕ}
    (L : ComplexEuclidean (k+1) ≃ₗᵢ[ℂ] ComplexEuclidean (k+1))
    (v : Fin ((2*k+1)+1) → ComplexEuclidean (k+1)) :
    sphereVolume k (L ∘ v) = sphereVolume k v := by
  have h := congrArg (fun A => A (v ∘ ambientFinEquiv k)) (interleavedVolume_unitary L)
  simpa only [sphereVolume, AlternatingMap.domDomCongr_apply,
    AlternatingMap.compLinearMap_apply, Function.comp_def, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using h

lemma normEnergy_boundaryFin_unitary {k : ℕ}
    (L : ComplexEuclidean (k+1) ≃ₗᵢ[ℂ] ComplexEuclidean (k+1))
    (x : ComplexEuclidean (k+1)) (v : Fin (2*k+1) → ComplexEuclidean (k+1)) :
    boundaryFormFin (dcLinear (normEnergy (k+1))) (L x) (L ∘ v) =
      boundaryFormFin (dcLinear (normEnergy (k+1))) x v := by
  have h := congrArg (fun A => A (v ∘ boundaryFinEquiv k)) (normEnergy_boundary_unitary L x k)
  simpa only [boundaryFormFin, AlternatingMap.domDomCongr_apply,
    AlternatingMap.compLinearMap_apply, Function.comp_def, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using h

lemma reference_boundaryFin_on_tangent {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1) (v : Fin (2*k+1) → ComplexEuclidean (k+1))
    (hv : ∀ i, inner ℝ x (v i) = 0) :
    boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x v =
      boundaryFormFin (dcLinear (normEnergy (k+1))) x v := by
  let w : Fin 1 ⊕ WedgePowerSlots k → sphereTangent x := fun s =>
    ⟨v (boundaryFinEquiv k s), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
  have h := congrArg (fun A => A w) (reference_sphere_boundaryForm hx k)
  simpa only [boundaryFormFin, AlternatingMap.domDomCongr_apply, tangentForm,
    ← wedgePower_compLinearMap, ← wedge_compLinearMap, AlternatingMap.compLinearMap_apply,
    Submodule.subtype_apply, w, Function.comp_def] using h

/-- The actual reference logarithmic boundary form has the constant outward
sphere density k!/2 in complex dimension k+1. -/
theorem reference_boundary_density {k : ℕ} {x : ComplexEuclidean (k+1)} (hx : ‖x‖ = 1) :
    orientedDensity (sphereFrame k) (sphereVolume k)
      (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x) x =
      (k.factorial : ℂ)/2 := by
  obtain ⟨L,hL⟩ := exists_unitary_referencePole hx
  let v := L ∘ poleFrameFin k
  have hv0 (i : Fin (2*k+1)) : inner ℝ (referencePole k) (poleFrameFin k i) = 0 := by
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (poleFrameVector_tangent _)
  have hv (i : Fin (2*k+1)) : inner ℝ x (v i) = 0 := by
    rw [← hL]
    exact (unitary_real_inner L _ _).trans (hv0 i)
  have hvol : sphereVolume k (Matrix.vecCons x v) = 1 := by
    have he : Matrix.vecCons x v = L ∘ Matrix.vecCons (referencePole k) (poleFrameFin k) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [Matrix.vecCons] using hL.symm
      · rfl
    rw [he, sphereVolume_unitary, poleFrameFin_volume]
  have hb : boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x v =
      (k.factorial : ℂ)/2 := by
    rw [reference_boundaryFin_on_tangent hx v hv, ← hL]
    exact (normEnergy_boundaryFin_unitary L (referencePole k) (poleFrameFin k)).trans
      (referencePole_boundaryFin_value k)
  have h := orientedDensity_spec (sphereFrame k) (sphereVolume k) (sphereVolume_frame_ne_zero k)
    (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x) hx v hv
  rw [hvol, mul_one, hb] at h
  exact h.symm

/-- Integration of the reference boundary form against Euclidean
sphere area, with outward orientation and the dc convention. -/
theorem reference_boundary_flux (k : ℕ) :
    sphereFlux k (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1))))) =
      Real.pi^(k+1) := by
  unfold sphereFlux
  convert reference_sphere_density_integral (k+1) (by omega) using 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : ‖(x : ComplexEuclidean (k+1))‖ = 1 := by
    simpa only [mem_sphere_iff_norm, sub_zero] using x.property
  rw [reference_boundary_density hx]
  simp

end Mahler

end OAI
