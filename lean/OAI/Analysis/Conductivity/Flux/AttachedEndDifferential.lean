import Mathlib
import OAI.Analysis.Conductivity.Geometry.CollarAE
import OAI.Analysis.Conductivity.Fourier.AttachedEndPoisson

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

theorem attachedEndPoisson_real_fderiv (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) (sourceCollarPiece i j x) v=
      (sourceCartesianGradientMatrix i j x *ᵥ (endAxialMatrix a *ᵥ
        (fun k : Fin 3 => (attachedEndPoissonField s f a b k.succ (sourceCollarPiece i j x)).re))) ⬝ᵥ v := by
  let E := sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)
  let z := endAxialAffine a b (sourceFaceAngles i j x)
  let r : Fin 3 → ℝ := fun k => (endPoissonField s f k.succ (z 0,torusAngles z)).re
  let w := E.symm v
  have hw : sourceCollarJacobian i j x *ᵥ w=v := E.apply_symm_apply v
  have hd : (sourceFaceAngleMatrix i j x)ᵀ=sourceFaceAngleMatrix i j x := Matrix.diagonal_transpose _
  have ha : (endAxialMatrix a)ᵀ=endAxialMatrix a := Matrix.diagonal_transpose _
  have hp := Complex.reCLM.hasFDerivAt.comp (sourceCollarPiece i j x)
    (attachedEndPoissonField_hasFDeriv s hs f a b i j hx ht)
  have hr : r=fun k : Fin 3 => (attachedEndPoissonField s f a b k.succ (sourceCollarPiece i j x)).re := by
    funext k
    obtain ⟨htx,hi,hj⟩ := mem_sourceExtendedBox.mp (sourceCollarOpenBox_subset hx)
    dsimp only [r,z]
    rw [←sourceFaceAngles_physical i j hi hj,attachedEndPoissonField_angular s f a b k.succ htx,
      torusAngles_endAxialAffine]
    rfl
  calc
    _ = (fderiv ℝ (endFlatPoisson s f) z
        (endAxialMatrix a *ᵥ (sourceFaceAngleMatrix i j x *ᵥ w))).re :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v) hp.fderiv
    _ = r ⬝ᵥ (endAxialMatrix a *ᵥ (sourceFaceAngleMatrix i j x *ᵥ w)) :=
      endFlatPoisson_realCLM_apply s hs f (x:=z) ht _
    _ = (sourceFaceAngleMatrix i j x *ᵥ w) ⬝ᵥ (endAxialMatrix a *ᵥ r) := by
      simpa only [ha] using Matrix.dotProduct_transpose_mulVec (endAxialMatrix a) r (sourceFaceAngleMatrix i j x *ᵥ w)
    _ = w ⬝ᵥ (sourceFaceAngleMatrix i j x *ᵥ (endAxialMatrix a *ᵥ r)) := by
      rw [dotProduct_comm (sourceFaceAngleMatrix i j x *ᵥ w) (endAxialMatrix a *ᵥ r)]
      simpa only [hd] using Matrix.dotProduct_transpose_mulVec (sourceFaceAngleMatrix i j x) (endAxialMatrix a *ᵥ r) w
    _ = w ⬝ᵥ ((sourceCollarJacobian i j x)ᵀ *ᵥ
        (sourceCartesianGradientMatrix i j x *ᵥ (endAxialMatrix a *ᵥ r))) := by
      rw [sourceCartesianGradient_chain i j (sourceCollarOpenBox_subset hx)]
    _ = (sourceCartesianGradientMatrix i j x *ᵥ (endAxialMatrix a *ᵥ r)) ⬝ᵥ
        (sourceCollarJacobian i j x *ᵥ w) := Matrix.dotProduct_transpose_mulVec _ _ _
    _ = _ := by rw [hw,hr]

lemma sourceCollarPiece_time_open {i j : Fin 4} {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) : sourceCollarTime (sourceCollarPiece i j x)=x 0 := by
  obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp (sourceCollarOpenBox_subset hx)
  rw [←sourceFaceAngles_physical i j hi hj,sourceAngular_time ht]

lemma attachedEndPoisson_real_differentiable_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) :
    ∀ᵐ y : Fin 3 → ℝ,y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      0<a*(sourceCollarTime y-b) → DifferentiableAt ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y := by
  filter_upwards [sourceCollar_open_charts_ae] with y hy hb ht
  obtain ⟨i,j,x,hx,rfl⟩ := hy hb
  rw [sourceCollarPiece_time_open hx] at ht
  exact (Complex.reCLM.hasFDerivAt.comp _ (attachedEndPoissonField_hasFDeriv s hs f a b i j hx ht)).differentiableAt

end ScalarConductivity

end

end OAI
