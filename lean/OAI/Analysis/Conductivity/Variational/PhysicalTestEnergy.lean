import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalFaceUniqueness

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def physicalTestCovector (φ : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => fderiv ℝ φ y (Pi.single k 1)

lemma clm_eq_coordinate_dot (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    L v=(fun k => L (Pi.single k 1)) ⬝ᵥ v := by
  have hv : v=∑ k : Fin 3,v k • Pi.single k (1:ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum,map_smul,smul_eq_mul,dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

def attachedFlatTestCovector (φ : (Fin 3 → ℝ) → ℝ) (a : ℝ)
    (i j : Fin 4) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (attachedCartesianMatrix a i j x)⁻¹ *ᵥ physicalTestCovector φ (sourceCollarPiece i j x)

lemma attachedFlatTestCovector_transport (φ : (Fin 3 → ℝ) → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    attachedCartesianMatrix a i j x*ᵥattachedFlatTestCovector φ a i j x=
      physicalTestCovector φ (sourceCollarPiece i j x) := by
  rw [attachedFlatTestCovector,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]

lemma physicalTestCovector_chain (φ : (Fin 3 → ℝ) → ℝ)
    (i j : Fin 4) (x : Fin 3 → ℝ)
    (hφ : DifferentiableAt ℝ φ (sourceCollarPiece i j x)) :
    physicalTestCovector (φ ∘ sourceCollarPiece i j) x=
      (sourceCollarJacobian i j x)ᵀ *ᵥ physicalTestCovector φ (sourceCollarPiece i j x) := by
  ext k
  rw [physicalTestCovector,(hφ.hasFDerivAt.comp x (sourceCollarPiece_hasFDeriv i j x)).fderiv]
  change fderiv ℝ φ (sourceCollarPiece i j x)
    (sourceCollarDerivative i j x (Pi.single k 1))=_
  change fderiv ℝ φ (sourceCollarPiece i j x)
    (sourceCollarJacobian i j x*ᵥPi.single k 1)=_
  rw [Matrix.mulVec_single_one,clm_eq_coordinate_dot]
  simp only [physicalTestCovector,Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  simp [Matrix.col,mul_comm]

theorem attachedFlatTestCovector_chain (φ : (Fin 3 → ℝ) → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (hφ : DifferentiableAt ℝ φ (sourceCollarPiece i j x)) :
    physicalTestCovector (φ ∘ sourceCollarPiece i j) x=
      sourceFaceAngleMatrix i j x*ᵥ(endAxialMatrix a*ᵥattachedFlatTestCovector φ a i j x) := by
  rw [physicalTestCovector_chain φ i j x hφ,
    ←attachedFlatTestCovector_transport φ ha i j hx,attachedCartesianMatrix,
    ←Matrix.mulVec_mulVec,sourceCartesianGradient_chain i j hx]

theorem attachedCollarTensor_test_energy (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (φ : (Fin 3 → ℝ) → ℝ)
    {a b : ℝ} (ha : a≠0) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    |(sourceCollarJacobian i j x).det| *
      (physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re)
        (sourceCollarPiece i j x) ⬝ᵥ
        (attachedCollarTensor s a (sourceCollarPiece i j x)*ᵥ
          physicalTestCovector φ (sourceCollarPiece i j x)))=
      |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
        ((fun k : Fin 3 => (endPoissonField s f k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re) ⬝ᵥ
          (flatCylinderMatrix s*ᵥattachedFlatTestCovector φ a i j x)) := by
  have hP : physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re)
      (sourceCollarPiece i j x)=attachedCartesianMatrix a i j x*ᵥ
        (fun k : Fin 3 => (endPoissonField s f k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re) := by
    ext k
    simp only [physicalTestCovector,attachedCartesianMatrix_poisson_derivative s hs f a b i j hx ht,
      dotProduct_single,mul_one]
  rw [hP,attachedCollarTensor_open s a i j hx,
    ←attachedFlatTestCovector_transport φ ha i j (sourceCollarOpenBox_subset hx)]
  exact attachedFlatTensor_energy_density s ha i j (sourceCollarOpenBox_subset hx) _ _

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceExtendedBox_open_ae {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x∈sourceCollarOpenBox := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier B := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc),
    ae_restrict_of_ae hn] with x hx hn
  have hxB : x∈B := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra h
  exact hn ⟨subset_closure hxB,h⟩

theorem attachedCollarTensor_test_integral (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (φ : (Fin 3 → ℝ) → ℝ)
    {a b l r : ℝ} (ha : a≠0) (i j : Fin 4)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (ht : ∀ t∈Icc l r,0<a*(t-b)) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
      physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re) y ⬝ᵥ
        (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      ∫ x in sourceExtendedBox l r,
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          ((fun k : Fin 3 => (endPoissonField s f k.succ
            (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re) ⬝ᵥ
            (flatCylinderMatrix s*ᵥattachedFlatTestCovector φ a i j x)) := by
  rw [sourceExtended_integral i j hl hr]
  apply integral_congr_ae
  filter_upwards [sourceExtendedBox_open_ae hl hr,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  simp only [smul_eq_mul]
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det]
  exact attachedCollarTensor_test_energy s hs f φ ha i j hx (ht (x 0) (mem_sourceExtendedBox.mp hm).1)

end ScalarConductivity

end

end OAI
