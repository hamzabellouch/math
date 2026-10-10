import Mathlib
import OAI.Analysis.Conductivity.Geometry.CollarLocalInverse
import OAI.Analysis.Conductivity.Fourier.EndPoissonDifferential

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma physicalEndPoissonField_piece (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    physicalEndPoissonField s f 0 (sourceCollarPiece i j x)=
      endFlatPoisson s f (sourceFaceAngles i j x) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [←sourceFaceAngles_physical i j ha hb,physicalEndPoissonField_angular s f 0 ht,
    endFlatPoisson_eq]
  rfl

lemma physicalEndPoissonField_local_eq (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    physicalEndPoissonField s f 0 =ᶠ[𝓝 (sourceCollarPiece i j x)]
      (fun y => endFlatPoisson s f (sourceFaceAngles i j (sourceCollarInverse i j y))) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),physicalEndPoissonField s f 0 y=
    endFlatPoisson s f (sourceFaceAngles i j (sourceCollarInverse i j y))
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx,
    sourceCollarInverse_eventually_left i j hx] with y hy hi
  rw [hi]
  exact physicalEndPoissonField_piece s f i j (sourceCollarOpenBox_subset hy)

lemma sourceCollarInverse_point (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) : sourceCollarInverse i j (sourceCollarPiece i j x)=x :=
  (sourceCollarInverse_eventually_left i j hx).self_of_nhds

theorem physicalEndPoissonField_hasFDeriv (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<x 0) :
    HasFDerivAt (physicalEndPoissonField s f 0)
      ((fderiv ℝ (endFlatPoisson s f) (sourceFaceAngles i j x)).comp
        (((Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap).comp
          (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.toContinuousLinearMap))
      (sourceCollarPiece i j x) := by
  have h1 := (sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt
  have h2 := sourceFaceAngles_hasFDeriv i j x
  have he := sourceCollarInverse_point i j hx
  have h2a : HasFDerivAt (sourceFaceAngles i j)
      (Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap
      (sourceCollarInverse i j (sourceCollarPiece i j x)) := by simpa only [he] using h2
  have h2' := h2a.comp (sourceCollarPiece i j x) h1
  have h3 := (endFlatPoisson_hasFDeriv s hs f (x:=sourceFaceAngles i j x) ht).differentiableAt.hasFDerivAt
  have h3a : HasFDerivAt (endFlatPoisson s f)
      (fderiv ℝ (endFlatPoisson s f) (sourceFaceAngles i j x))
      (sourceFaceAngles i j (sourceCollarInverse i j (sourceCollarPiece i j x))) := by
    simpa only [he] using h3
  have h3' := h3a.comp (sourceCollarPiece i j x) h2'
  exact h3'.congr_of_eventuallyEq (physicalEndPoissonField_local_eq s f i j hx)

lemma realCLM_apply_basis {n : Type*} [Fintype n] [DecidableEq n]
    (L : (n → ℝ) →L[ℝ] ℝ) (v : n → ℝ) :
    L v = (fun k => L (Pi.single k 1)) ⬝ᵥ v := by
  have hv : (∑ k,Pi.single k (v k))=v := LinearMap.sum_single_apply (fun _ : n => ℝ) v
  conv_lhs => rw [←hv]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : Pi.single k (v k)=v k • Pi.single k (1:ℝ) := by
    rw [←Pi.single_smul]; simp
  rw [hk,map_smul]
  change v k*L (Pi.single k 1)=L (Pi.single k 1)*v k
  ring

lemma endFlatPoisson_realCLM_apply (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) (v : Fin 3 → ℝ) :
    (fderiv ℝ (endFlatPoisson s f) x v).re=
      (fun k : Fin 3 => (endPoissonField s f k.succ (x 0,torusAngles x)).re) ⬝ᵥ v := by
  change (Complex.reCLM.comp (fderiv ℝ (endFlatPoisson s f) x)) v=_
  rw [realCLM_apply_basis]
  apply congrArg (fun g : Fin 3 → ℝ => g ⬝ᵥ v)
  funext k
  exact congrArg Complex.re (endFlatPoisson_derivative_axis s hs f hx k)

theorem physicalEndPoisson_real_fderiv (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<x 0) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (physicalEndPoissonField s f 0 y).re) (sourceCollarPiece i j x) v=
      (sourceCartesianGradientMatrix i j x *ᵥ
        (fun k : Fin 3 => (endPoissonField s f k.succ
          (x 0,torusAngles (sourceFaceAngles i j x))).re)) ⬝ᵥ v := by
  let E := sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)
  let r : Fin 3 → ℝ := fun k =>
    (endPoissonField s f k.succ (x 0,torusAngles (sourceFaceAngles i j x))).re
  let w := E.symm v
  have hw : sourceCollarJacobian i j x *ᵥ w=v := E.apply_symm_apply v
  have hd : (sourceFaceAngleMatrix i j x)ᵀ=sourceFaceAngleMatrix i j x :=
    Matrix.diagonal_transpose _
  have hp := Complex.reCLM.hasFDerivAt.comp (sourceCollarPiece i j x)
    (physicalEndPoissonField_hasFDeriv s hs f i j hx ht)
  calc
    _ = (fderiv ℝ (endFlatPoisson s f) (sourceFaceAngles i j x)
        (sourceFaceAngleMatrix i j x *ᵥ w)).re :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v) hp.fderiv
    _ = r ⬝ᵥ (sourceFaceAngleMatrix i j x *ᵥ w) :=
      endFlatPoisson_realCLM_apply s hs f (x:=sourceFaceAngles i j x) ht _
    _ = w ⬝ᵥ (sourceFaceAngleMatrix i j x *ᵥ r) := by
      rw [←Matrix.dotProduct_transpose_mulVec,hd]
    _ = w ⬝ᵥ ((sourceCollarJacobian i j x)ᵀ *ᵥ
        (sourceCartesianGradientMatrix i j x *ᵥ r)) := by
      rw [sourceCartesianGradient_chain i j (sourceCollarOpenBox_subset hx)]
    _ = (sourceCartesianGradientMatrix i j x *ᵥ r) ⬝ᵥ
        (sourceCollarJacobian i j x *ᵥ w) := Matrix.dotProduct_transpose_mulVec _ _ _
    _ = _ := by rw [hw]

end ScalarConductivity

end

end OAI
