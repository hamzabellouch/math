import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralJetIdentity
import OAI.Analysis.Conductivity.Flux.CylinderSlopeGreen

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma central_cylinder_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (slopes R : Fin 3 → ℝ) (hR : ∀ i,0<R i) (p : centralEnergySpace s)
    (hp : ∀ v : centralEnergySpace s,
      inner ℝ (centralD s p) (centralD s v)+
        angularArea*(∑ i : Fin 3,inner ℝ
          (spectralGraphWeight (torusRate s) (centralT s i p))
          (spectralGraphWeight (torusRate s) (centralT s i v)))=
        angularArea*(∑ i : Fin 3,slopes i*
          spectralGraphMean (torusRate s) (centralT s i v)))
    (v : centralEnergySpace s) (z : (i : Fin 3) → cylinderSobolevGraph s (R i))
    (hz : ∀ i,(z i).val.2.1=centralT s i v) :
    inner ℝ (centralD s p) (centralD s v)+angularArea*(∑ i : Fin 3,
      (flatCylinderEnergy s
        (cylinderEndJet s hs (slopes i) (R i) (hR i).le (centralT s i p)) (z i).val.1).re)=
      angularArea*(∑ i : Fin 3,cylinderTerminalFlux s (slopes i) (R i)
        (centralT s i p) (z i).val.2.2) := by
  have he (i : Fin 3) := cylinderEndJet_real_green s hs (slopes i) (hR i)
    (centralT s i p) (z i)
  simp only [hz] at he
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  nlinarith [hp v]

theorem central_attached_weak_solution_exists (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (a slopes : Fin 3 → ℝ) (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)
    (hslopes : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,∃ w : H1,w∈H10 ∧ centralM s p=0 ∧
      (w.val=ᵐ[ballMeasure] (fun x =>
        (centralNeighborhoodCompletion s hs ha₀ ha p).val x+
          centralSlopeJet a slopes (WithLp.ofLp x))) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
        w.val x=centralFullJetCLM s p.val x) ∧
      (∀ (R : Fin 3 → ℝ) (hR : ∀ i,0<R i),
        (∀ i,(cylinderEndJet s hs (slopes i) (R i) (hR i).le (centralT s i p),
          (centralT s i p,spectralPoissonTrace s (R i) (centralT s i p)+
            spectralTraceSingleL s 0 ((slopes i:ℂ)*(R i:ℂ))))∈cylinderSobolevGraph s (R i)) ∧
        (∀ (v : centralEnergySpace s) (z : (i : Fin 3) → cylinderSobolevGraph s (R i)),
          (∀ i,(z i).val.2.1=centralT s i v) →
          inner ℝ (centralD s p) (centralD s v)+angularArea*(∑ i : Fin 3,
            (flatCylinderEnergy s
              (cylinderEndJet s hs (slopes i) (R i) (hR i).le (centralT s i p)) (z i).val.1).re)=
            angularArea*(∑ i : Fin 3,cylinderTerminalFlux s (slopes i) (R i)
              (centralT s i p) (z i).val.2.2))) := by
  obtain ⟨p,w,hw,hm,he,hc,hvar⟩ :=
    central_variational_neighborhood_exists s hs a slopes ha₀ ha hslopes
  refine ⟨p,w,hw,hm,he,hc,fun R hR => ⟨?_,?_⟩⟩
  · intro i
    exact cylinderEndJet_mem_graph s hs (slopes i) (R i) (hR i).le (centralT s i p)
  · intro v z hz
    exact central_cylinder_green s hs slopes R hR p hvar v z hz

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def flatCylinderMatrix (s : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1,0,0],![0,s 0,s 1],![0,s 1,s 2]]

lemma flatCylinderMatrix_symmetric (s : Fin 3 → ℝ) :
    (flatCylinderMatrix s)ᵀ=flatCylinderMatrix s := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma flatCylinderMatrix_energy (s v : Fin 3 → ℝ) :
    v ⬝ᵥ (flatCylinderMatrix s *ᵥ v)=
      (v 0)^2+s 0*(v 1)^2+2*s 1*v 1*v 2+s 2*(v 2)^2 := by
  simp [flatCylinderMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

lemma flatCylinderMatrix_coercive (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (v : Fin 3 → ℝ) :
    (1/2)*(∑ k : Fin 3,(v k)^2)≤v ⬝ᵥ (flatCylinderMatrix s *ᵥ v) := by
  rw [flatCylinderMatrix_energy]
  simp only [Fin.sum_univ_succ,Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,Fin.isValue,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  nlinarith [hs (v 1) (v 2),sq_nonneg (v 0)]

lemma sourceFaceAngleMatrix_det (i j : Fin 4) (x : Fin 3 → ℝ) :
    (sourceFaceAngleMatrix i j x).det=
      angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2) := by
  rw [sourceFaceAngleMatrix,Matrix.det_diagonal]
  simp [Fin.prod_univ_succ,angularArea]
  ring

lemma sourceFaceAngleMatrix_det_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    0<(sourceFaceAngleMatrix i j x).det := by
  obtain ⟨_,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [sourceFaceAngleMatrix_det]
  have h0 := (faceRayDensityLower_pos (w:=1) (by norm_num)).trans_le
    (faceRayDensity_lower (w:=1) (by norm_num) i ha)
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have h1 := (faceRayDensityLower_pos hw).trans_le (faceRayDensity_lower hw j hb)
  exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one angularArea_ge_one) h0) h1

lemma sourceCartesianGradientMatrix_det_ne_zero (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    (sourceCartesianGradientMatrix i j x).det≠0 := by
  rw [sourceCartesianGradientMatrix,Matrix.det_mul,Matrix.det_nonsing_inv,
    Matrix.det_transpose,Ring.inverse_eq_inv']
  exact mul_ne_zero (inv_ne_zero (sourceCollarJacobian_extended_ne_zero i j hx))
    (sourceFaceAngleMatrix_det_pos i j hx).ne'

def sourceFlatDensity (i j : Fin 4) (x : Fin 3 → ℝ) : ℝ :=
  (sourceFaceAngleMatrix i j x).det/|(sourceCollarJacobian i j x).det|

lemma sourceFlatDensity_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    0<sourceFlatDensity i j x :=
  div_pos (sourceFaceAngleMatrix_det_pos i j hx)
    (abs_pos.mpr (sourceCollarJacobian_extended_ne_zero i j hx))

def sourceFlatTensor (s : Fin 3 → ℝ) (i j : Fin 4) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  sourceFlatDensity i j x •
    (((sourceCartesianGradientMatrix i j x)⁻¹)ᵀ*flatCylinderMatrix s*
      (sourceCartesianGradientMatrix i j x)⁻¹)

lemma sourceFlatTensor_symmetric (s : Fin 3 → ℝ) (i j : Fin 4) (x : Fin 3 → ℝ) :
    (sourceFlatTensor s i j x)ᵀ=sourceFlatTensor s i j x := by
  simp only [sourceFlatTensor,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose,flatCylinderMatrix_symmetric,Matrix.mul_assoc]

lemma inverse_congruence_energy (C K : Matrix (Fin 3) (Fin 3) ℝ)
    (hC : C.det≠0) (d : ℝ) (v w : Fin 3 → ℝ) :
    (C*ᵥv) ⬝ᵥ ((d • (C⁻¹ᵀ*K*C⁻¹))*ᵥ(C*ᵥw))=
      d*(v ⬝ᵥ (K*ᵥw)) := by
  have hi (u : Fin 3 → ℝ) : C⁻¹*ᵥ(C*ᵥu)=u := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hC),Matrix.one_mulVec]
  rw [Matrix.smul_mulVec,dotProduct_smul]
  change d*((C*ᵥv) ⬝ᵥ ((C⁻¹ᵀ*K*C⁻¹)*ᵥ(C*ᵥw)))=_
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hi,
    Matrix.dotProduct_transpose_mulVec,hi,dotProduct_comm]

theorem sourceFlatTensor_energy (s : Fin 3 → ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v w : Fin 3 → ℝ) :
    (sourceCartesianGradientMatrix i j x*ᵥv) ⬝ᵥ
      (sourceFlatTensor s i j x*ᵥ(sourceCartesianGradientMatrix i j x*ᵥw))=
      sourceFlatDensity i j x*(v ⬝ᵥ (flatCylinderMatrix s*ᵥw)) :=
  inverse_congruence_energy _ _ (sourceCartesianGradientMatrix_det_ne_zero i j hx) _ _ _

theorem sourceFlatTensor_energy_density (s : Fin 3 → ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v w : Fin 3 → ℝ) :
    |(sourceCollarJacobian i j x).det| *((sourceCartesianGradientMatrix i j x*ᵥv) ⬝ᵥ
      (sourceFlatTensor s i j x*ᵥ(sourceCartesianGradientMatrix i j x*ᵥw)))=
      angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
        (v ⬝ᵥ (flatCylinderMatrix s*ᵥw)) := by
  rw [sourceFlatTensor_energy s i j hx,sourceFlatDensity,sourceFaceAngleMatrix_det]
  field_simp [abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx)]

end ScalarConductivity

end

end OAI
