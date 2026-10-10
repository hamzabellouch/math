import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalTestEnergy
import OAI.Analysis.Conductivity.Branching.ParentCompletedEndJet
import OAI.Analysis.Conductivity.Branching.ParentEndPartition
import OAI.Analysis.Conductivity.Variational.EndPartitionJet

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem parentFullEnd_H10 (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      WithLp.ofLp x∈sourceClosedCollarBand 0 centralThickness →
      weakValue w x=fullAttachedEndValue s (centralT s 0 p) a centralThickness κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=
        fullAttachedEndGradient s (centralT s 0 p) a centralThickness κ (WithLp.ofLp x) i) := by
  obtain ⟨χ,η,hχ,hχc,hχb,hχs,hη,hηc,hηb,hηs,hpart⟩ := parent_end_partition_exists
  generalize hU : parentCompletionJoin s hs ha hχ hχc hχb hχs p = u
  have hu : u∈H10 := by
    rw [←hU]
    exact parentCompletionJoin_mem_H10 s hs ha hχ hχc hχb hχs p
  have hue := parentCompletionJoin_end_ae s hs ha hχ hχc hχb hχs p
  rw [hU] at hue
  obtain ⟨v,hv,hve⟩ := compact_collar_slope_value_gradient hχ hχc hχb ha.ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    κ 0 (2*centralThickness) (by norm_num) (by norm_num [centralThickness]) hχs
  have hR : 0≤-a*(3*centralThickness/2) :=
    mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness])
  have hT : ∀ t∈Icc (-centralThickness/2) (3*centralThickness/4),
      affineEndTime a centralThickness t∈Icc 0 (-a*(3*centralThickness/2)) := by
    intro t ht
    dsimp only [affineEndTime]
    constructor
    · apply mul_nonneg_of_nonpos_of_nonpos ha.le
      dsimp [centralThickness] at *
      linarith [ht.2]
    · have hm := mul_nonpos_of_nonpos_of_nonneg ha.le
        (sub_nonneg.mpr ht.1)
      nlinarith
  have hpos : ∀ t∈Icc (-centralThickness/2) (3*centralThickness/4),
      0<a*(t-centralThickness) := by
    intro t ht
    apply mul_pos_of_neg_of_neg ha
    dsimp [centralThickness] at *
    linarith [ht.2]
  obtain ⟨z,hz,hze⟩ := cut_fullAttachedEnd_H10 s hs (centralT s 0 p) κ ha.ne hR
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    (show -centralThickness/2≤3*centralThickness/4 by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    hT hpos hη hηc hηb hηs
  refine ⟨u+v+z,H10.add_mem (H10.add_mem hu hv) hz,?_⟩
  have hne := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
        norm_num [centralThickness])))
  apply fullEnd_partition_jet s (centralT s 0 p) a centralThickness κ hχ hη hpart
      (u:=u) (v:=v) (z:=z) _ hue hve hze
  filter_upwards [hne] with x hnx hx
  exact mul_pos_of_neg_of_neg ha (sub_neg.mpr (lt_of_le_of_ne hx.2 hnx))

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma sourceCollarTime_local_inverse (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    sourceCollarTime=ᶠ[𝓝 (sourceCollarPiece i j x)]
      (fun y => sourceCollarInverse i j y 0) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),sourceCollarTime y=sourceCollarInverse i j y 0
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx,
    sourceCollarInverse_eventually_left i j hx] with y hy hi
  rw [hi,sourceCollarPiece_time_open hy]

lemma sourceCollarTime_differentiable_open (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    DifferentiableAt ℝ sourceCollarTime (sourceCollarPiece i j x) := by
  have hd := (sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt.differentiableAt
  exact ((differentiableAt_pi.mp hd) 0).congr_of_eventuallyEq
    (sourceCollarTime_local_inverse i j hx)

lemma attachedCartesianMatrix_axial_derivative (a b : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    physicalTestCovector (fun y => a*(sourceCollarTime y-b)) (sourceCollarPiece i j x)=
      attachedCartesianMatrix a i j x*ᵥPi.single 0 1 := by
  let F : (Fin 3 → ℝ) → ℝ := fun y => a*(sourceCollarTime y-b)
  have hd : DifferentiableAt ℝ F (sourceCollarPiece i j x) :=
    ((sourceCollarTime_differentiable_open i j hx).sub_const b).const_mul a
  have he : (F ∘ sourceCollarPiece i j)=ᶠ[𝓝 x] (fun y => a*(y 0-b)) := by
    filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx] with y hy
    simp only [Function.comp_apply,F,sourceCollarPiece_time_open hy]
  have hf : physicalTestCovector (F ∘ sourceCollarPiece i j) x=Pi.single 0 a := by
    ext k
    rw [physicalTestCovector,he.fderiv_eq,
      (((hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x).sub_const b).const_mul a).fderiv]
    fin_cases k <;> simp
  have hc := physicalTestCovector_chain F i j x hd
  have ht : (sourceCollarJacobian i j x)ᵀ *ᵥ
      (attachedCartesianMatrix a i j x*ᵥPi.single 0 1)=Pi.single 0 a := by
    rw [attachedCartesianMatrix,←Matrix.mulVec_mulVec,
      sourceCartesianGradient_chain i j (sourceCollarOpenBox_subset hx)]
    ext k
    fin_cases k <;> simp [sourceFaceAngleMatrix,endAxialMatrix,Matrix.mulVec_diagonal]
  have hn : IsUnit (sourceCollarJacobian i j x)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j (sourceCollarOpenBox_subset hx))
  have hh := congrArg (fun v => (sourceCollarJacobian i j x)ᵀ⁻¹*ᵥv)
    (hc.symm.trans (hf.trans ht.symm))
  simpa only [Matrix.mulVec_mulVec,←Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hn,
    Matrix.one_mulVec,Matrix.one_mul] using hh

def fullEndFlatCovector (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (κ : ℝ) (t : ℝ) (θ : (Fin 2 → UnitAddCircle)) : Fin 3 → ℝ :=
  (fun k => (endPoissonField s f k.succ (t,θ)).re)+κ • Pi.single 0 1

lemma fullAttachedEnd_covector (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b κ : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    physicalTestCovector (fullAttachedEndValue s f a b κ) (sourceCollarPiece i j x)=
      fullAttachedEndGradient s f a b κ (sourceCollarPiece i j x) := by
  have hp := (Complex.reCLM.hasFDerivAt.comp _
    (attachedEndPoissonField_hasFDeriv s hs f a b i j hx ht)).differentiableAt
  change DifferentiableAt ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re)
    (sourceCollarPiece i j x) at hp
  have hq := ((sourceCollarTime_differentiable_open i j hx).sub_const b).const_mul a
  ext k
  change fderiv ℝ ((fun y => (attachedEndPoissonField s f a b 0 y).re)+
    (fun y => κ*(a*(sourceCollarTime y-b)))) (sourceCollarPiece i j x) (Pi.single k 1)=_
  rw [(hp.hasFDerivAt.add (hq.hasFDerivAt.const_mul κ)).fderiv]
  rfl

lemma fullAttachedEndGradient_transport (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b κ : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    fullAttachedEndGradient s f a b κ (sourceCollarPiece i j x)=
      attachedCartesianMatrix a i j x*ᵥ
        fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) := by
  have hp : physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re)
      (sourceCollarPiece i j x)=attachedCartesianMatrix a i j x*ᵥ
        (fun k : Fin 3 => (endPoissonField s f k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re) := by
    ext k
    simp only [physicalTestCovector,attachedCartesianMatrix_poisson_derivative s hs f a b i j hx ht,
      dotProduct_single,mul_one]
  change physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re)
      (sourceCollarPiece i j x)+κ •
        physicalTestCovector (fun y => a*(sourceCollarTime y-b)) (sourceCollarPiece i j x)=_
  rw [hp,attachedCartesianMatrix_axial_derivative a b i j hx,fullEndFlatCovector,
    Matrix.mulVec_add,Matrix.mulVec_smul]

theorem fullAttachedEnd_test_energy (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) (φ : (Fin 3 → ℝ) → ℝ)
    {a b : ℝ} (ha : a≠0) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    |(sourceCollarJacobian i j x).det| *
      (fullAttachedEndGradient s f a b κ (sourceCollarPiece i j x) ⬝ᵥ
        (attachedCollarTensor s a (sourceCollarPiece i j x)*ᵥ
          physicalTestCovector φ (sourceCollarPiece i j x)))=
      |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
        (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
          (flatCylinderMatrix s*ᵥattachedFlatTestCovector φ a i j x)) := by
  rw [fullAttachedEndGradient_transport s hs f a b κ i j hx ht,
    attachedCollarTensor_open s a i j hx,
    ←attachedFlatTestCovector_transport φ ha i j (sourceCollarOpenBox_subset hx)]
  exact attachedFlatTensor_energy_density s ha i j (sourceCollarOpenBox_subset hx) _ _

theorem fullAttachedEnd_test_integral (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) (φ : (Fin 3 → ℝ) → ℝ)
    {a b l r : ℝ} (ha : a≠0) (i j : Fin 4)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (ht : ∀ t∈Icc l r,0<a*(t-b)) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
      fullAttachedEndGradient s f a b κ y ⬝ᵥ
        (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      ∫ x in sourceExtendedBox l r,
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
            (flatCylinderMatrix s*ᵥattachedFlatTestCovector φ a i j x)) := by
  rw [sourceExtended_integral i j hl hr]
  apply integral_congr_ae
  filter_upwards [sourceExtendedBox_open_ae hl hr,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  simp only [smul_eq_mul]
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det]
  exact fullAttachedEnd_test_energy s hs f κ φ ha i j hx (ht (x 0) (mem_sourceExtendedBox.mp hm).1)

end ScalarConductivity

end

end OAI
