import OAI.Geometry.NodalSets.Charts.SphereChartVolume

namespace OAI

namespace Yau.Target
open Manifold
noncomputable section
attribute [local instance] finrank_real_complex_fact'
abbrev CircleModel := EuclideanSpace ℝ (Fin 1)

def circleChartDerivative (p : Circle) (y : CircleModel) : CircleModel →L[ℝ] ℂ :=
  (show TangentSpace (𝓡 1) ((extChartAt (𝓡 1) p).symm y) →L[ℝ] ℂ from
    mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) ((extChartAt (𝓡 1) p).symm y)).comp
    (mfderiv 𝓘(ℝ,CircleModel) (𝓡 1) (extChartAt (𝓡 1) p).symm y)

def circleChartFactor (p : Circle) (y : CircleModel) : ℝ :=
  ‖circleChartDerivative p y (EuclideanSpace.basisFun (Fin 1) ℝ 0)‖^2

lemma circleChartDerivative_injective (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    Function.Injective (circleChartDerivative p y) := by
  apply (injective_mvfderiv_subtypeVal_sphere (n := 1) ((extChartAt (𝓡 1) p).symm y)).comp
  have h := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 1) hy).injective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
  convert! h using 1

lemma circleChartFactor_pos (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) : 0 < circleChartFactor p y := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  have he := circleChartDerivative_injective p hy (h.trans (map_zero _).symm)
  exact (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.ne_zero 0 he

lemma circleChartDerivative_inner_basis (p : Circle) (y : CircleModel) (i j : Fin 1) :
    @inner ℝ ℂ _ (circleChartDerivative p y (EuclideanSpace.basisFun (Fin 1) ℝ i))
      (circleChartDerivative p y (EuclideanSpace.basisFun (Fin 1) ℝ j)) =
      circleChartFactor p y := by
  rw [Subsingleton.elim i 0,Subsingleton.elim j 0,real_inner_self_eq_norm_sq]
  rfl

end
end Yau.Target

end OAI
