import OAI.Geometry.SurfaceImmersion.Geometry.NormalDefectJet

namespace OAI

/-! The original derivative-direction transversality is exactly the
three-column block entering the normal-defect jet. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceDirection_true_block {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (p : Base) :
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.comp
      (fderiv ℝ (surfaceDirection φ true) (p,0)) =
    directionBlock (fderiv ℝ (fun x => coordinateDifferential φ x (![0,1] : Base)) p)
      (transverseDerivative φ p) := by
  let E := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
  let W := fun x => coordinateDifferential φ x (![0,1] : Base)
  let U := transverseDerivative φ
  have hW : ContDiff ℝ ∞ W := (coordinateDifferential_smooth hφ).clm_apply contDiff_const
  have hU : ContDiff ℝ ∞ U := transverseDerivative_smooth hφ
  have hWD := (hW.differentiable (by simp) p).hasFDerivAt.comp (p,(0:ℝ)) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p,(0:ℝ))))
  have hUD := (hU.differentiable (by simp) p).hasFDerivAt.comp (p,(0:ℝ)) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p,(0:ℝ))))
  have hd := hWD.add ((hasFDerivAt_snd (𝕜 := ℝ) (p := (p,(0:ℝ)))).smul hUD)
  have hEq : E ∘ surfaceDirection φ true =
      fun z : Base × ℝ => W z.1 + z.2 • U z.1 := by
    funext z
    have hray : tangentRay true z.2 = (z.2) • (![1,0] : Base) + (![0,1] : Base) := by
      ext i
      fin_cases i <;> simp [tangentRay]
    simp only [Function.comp_apply,surfaceDirection,hray,map_add,map_smul]
    dsimp [W,U,transverseDerivative,coordinateDifferential,E]
    abel
  have hleft := E.hasFDerivAt.comp (p,(0:ℝ)) ((surfaceDirection_smooth hφ true).differentiable (by simp) _).hasFDerivAt
  change HasFDerivAt (fun z : Base × ℝ => W z.1 + z.2 • U z.1) _ (p,0) at hd
  have hfd := hleft.fderiv
  rw [hEq,hd.fderiv] at hfd
  rw [← hfd]
  apply ContinuousLinearMap.ext
  intro z
  simp [directionBlock_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,W,U]

lemma normalDefect_nondegenerate_of_direction {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : Fin 3 → ℝ) (p : Base)
    (hu : transverseDerivative φ p ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ p ≠ a)
    (hz : fderiv ℝ φ p (![0,1] : Base) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ true) (p,0))) :
    Function.Bijective (fderiv ℝ (normalDefect φ a) p) := by
  apply normalDefect_jet_bijective hφ a p hu ha hz
  rw [← surfaceDirection_true_block hφ p]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).bijective.comp hreg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
