import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalFlatEllipticity

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def attachedCartesianMatrix (a : ℝ) (i j : Fin 4) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := sourceCartesianGradientMatrix i j x*endAxialMatrix a

lemma attachedCartesianMatrix_det_ne_zero {a : ℝ} (ha : a≠0) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    (attachedCartesianMatrix a i j x).det≠0 := by
  rw [attachedCartesianMatrix,Matrix.det_mul]
  apply mul_ne_zero (sourceCartesianGradientMatrix_det_ne_zero i j hx)
  simpa [endAxialMatrix,Matrix.det_diagonal,Fin.prod_univ_succ] using ha

def attachedFlatTensor (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (|a| *sourceFlatDensity i j x) •
    (((attachedCartesianMatrix a i j x)⁻¹)ᵀ*flatCylinderMatrix s*
      (attachedCartesianMatrix a i j x)⁻¹)

lemma attachedFlatTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (x : Fin 3 → ℝ) : (attachedFlatTensor s a i j x)ᵀ=attachedFlatTensor s a i j x := by
  simp only [attachedFlatTensor,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose,flatCylinderMatrix_symmetric,Matrix.mul_assoc]

lemma attachedFlatTensor_energy (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v w : Fin 3 → ℝ) :
    (attachedCartesianMatrix a i j x*ᵥv) ⬝ᵥ
      (attachedFlatTensor s a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥw))=
        |a| *sourceFlatDensity i j x*(v ⬝ᵥ (flatCylinderMatrix s*ᵥw)) :=
  inverse_congruence_energy _ _ (attachedCartesianMatrix_det_ne_zero ha i j hx) _ _ _

lemma attachedFlatTensor_energy_density (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v w : Fin 3 → ℝ) :
    |(sourceCollarJacobian i j x).det| *((attachedCartesianMatrix a i j x*ᵥv) ⬝ᵥ
      (attachedFlatTensor s a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥw)))=
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (v ⬝ᵥ (flatCylinderMatrix s*ᵥw)) := by
  rw [attachedFlatTensor_energy s ha i j hx,sourceFlatDensity,sourceFaceAngleMatrix_det]
  field_simp [abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx)]

lemma flat_inverse_congruence_positive (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.det≠0) {d : ℝ} (hd : 0<d)
    {v : Fin 3 → ℝ} (hv : v≠0) :
    0<v ⬝ᵥ ((d • (C⁻¹ᵀ*flatCylinderMatrix s*C⁻¹))*ᵥv) := by
  let u := C⁻¹*ᵥv
  have hu : C*ᵥu=v := by
    change C*ᵥ(C⁻¹*ᵥv)=v
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC),Matrix.one_mulVec]
  have hn : u≠0 := by
    intro h
    rw [h,Matrix.mulVec_zero] at hu
    exact hv hu.symm
  have hex : ∃ k,u k≠0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  obtain ⟨k,hk⟩ := hex
  have hsum : 0<∑ l : Fin 3,(u l)^2 :=
    (sq_pos_of_ne_zero hk).trans_le (Finset.single_le_sum
      (fun l _ => sq_nonneg (u l)) (Finset.mem_univ k))
  have he := inverse_congruence_energy C (flatCylinderMatrix s) hC d u u
  rw [hu] at he
  rw [he]
  exact mul_pos hd ((mul_pos (by norm_num : (0:ℝ)<1/2) hsum).trans_le
    (flatCylinderMatrix_coercive s hs u))

lemma continuousOn_attachedCartesianMatrix (a : ℝ) (i j : Fin 4) :
    ContinuousOn (attachedCartesianMatrix a i j) (sourceExtendedBox (-(1:ℝ)/100) (1/100)) :=
  (continuousOn_sourceCartesianGradientMatrix i j).mul continuousOn_const

lemma continuousOn_attachedFlatTensor (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0) (i j : Fin 4) :
    ContinuousOn (attachedFlatTensor s a i j) (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  have hi : ContinuousOn (fun x => (attachedCartesianMatrix a i j x)⁻¹)
      (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
    intro x hx
    have hn := attachedCartesianMatrix_det_ne_zero ha i j hx
    exact (continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hn)).comp_continuousWithinAt
        (continuousOn_attachedCartesianMatrix a i j x hx)
  exact (continuousOn_const.mul (continuousOn_sourceFlatDensity i j)).smul
    ((((continuous_id.matrix_transpose :
        Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => Aᵀ)).comp_continuousOn hi).mul
          continuousOn_const).mul hi)

theorem attachedFlatTensor_elliptic (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a : ℝ} (ha : a≠0) (i j : Fin 4) :
    ∃ c C : ℝ,0<c ∧ c<C ∧ ∀ x∈sourceExtendedBox (-(1:ℝ)/100) (1/100),
      ∀ v : Fin 3 → ℝ,c*‖v‖^2≤v ⬝ᵥ (attachedFlatTensor s a i j x*ᵥv) ∧
        v ⬝ᵥ (attachedFlatTensor s a i j x*ᵥv)≤C*‖v‖^2 := by
  apply compact_matrix_energy_bounds isCompact_Icc _ (continuousOn_attachedFlatTensor s ha i j)
  intro x hx v hv
  exact flat_inverse_congruence_positive s hs _ (attachedCartesianMatrix_det_ne_zero ha i j hx)
    (mul_pos (abs_pos.mpr ha) (sourceFlatDensity_pos i j hx)) hv

lemma attachedCartesianMatrix_poisson_derivative (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) (sourceCollarPiece i j x) v=
      (attachedCartesianMatrix a i j x*ᵥ(fun k : Fin 3 =>
        (endPoissonField s f k.succ (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re)) ⬝ᵥ v := by
  rw [attachedEndPoisson_real_fderiv s hs f a b i j hx ht]
  have hfield (k : Fin 3) : attachedEndPoissonField s f a b k.succ (sourceCollarPiece i j x)=
      endPoissonField s f k.succ (a*(x 0-b),torusAngles (sourceFaceAngles i j x)) := by
    obtain ⟨htx,hi,hj⟩ := mem_sourceExtendedBox.mp (sourceCollarOpenBox_subset hx)
    rw [←sourceFaceAngles_physical i j hi hj,attachedEndPoissonField_angular s f a b k.succ htx]
  simp_rw [hfield]
  rw [attachedCartesianMatrix,Matrix.mulVec_mulVec]

end ScalarConductivity

end

end OAI
