import OAI.Geometry.NodalSets.Elliptic.Divergence
import OAI.Geometry.NodalSets.Waves.FiniteWaveDerivativeBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma coordPartial_finite_sum (V : ι → Coord → ℂ)
    (hV : ∀ a, Differentiable ℝ (V a)) (i : Fin 4) :
    coordPartial i (fun x ↦ ∑ a, V a x) = fun x ↦ ∑ a, coordPartial i (V a) x := by
  funext x
  simp only [coordPartial, fderiv_fun_sum (fun a _ ↦ hV a x),
    sum_apply]

lemma coordPartial_real_projection (u : Coord → ℂ) (hu : Differentiable ℝ u) (i : Fin 4) :
    coordPartial i (fun x ↦ ((u x).re : ℂ)) = fun x ↦ ((coordPartial i u x).re : ℂ) := by
  funext x
  have hr : DifferentiableAt ℝ (fun z ↦ (u z).re) x :=
    Complex.reCLM.differentiableAt.comp x (hu x)
  rw [coordPartial_ofReal_at (fun z ↦ (u z).re) x hr,
    realPart_fderiv u x (hu x)]
  rfl

lemma sourceFlux_finite_sum
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (V : ι → Coord → ℂ) (hV : ∀ a, Differentiable ℝ (V a)) (i : Fin 4) :
    sourceFlux g w (fun x ↦ ∑ a, V a x) i = fun x ↦ ∑ a, sourceFlux g w (V a) i x := by
  funext x
  simp only [sourceFlux, coordPartial_finite_sum V hV, Finset.mul_sum]
  exact Finset.sum_comm

lemma sourceFlux_const_mul
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (c : ℂ) (i : Fin 4) :
    sourceFlux g w (fun x ↦ c*u x) i = fun x ↦ c*sourceFlux g w u i x := by
  funext x
  simp only [sourceFlux, coordPartial_const_mul hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sourceFlux_real_projection
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (u : Coord → ℂ) (hu : Differentiable ℝ u) (i : Fin 4) :
    sourceFlux g w (fun x ↦ ((u x).re:ℂ)) i = fun x ↦ ((sourceFlux g w u i x).re:ℂ) := by
  funext x
  simp [sourceFlux,coordPartial_real_projection u hu,Complex.mul_re]

lemma sourceWeightedOperator_finite_sum
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (V : ι → Coord → ℂ) (hV : ∀ a, Differentiable ℝ (V a))
    (hf : ∀ a i, Differentiable ℝ (sourceFlux g w (V a) i)) :
    sourceWeightedOperator g w (fun x ↦ ∑ a, V a x) =
      fun x ↦ ∑ a, sourceWeightedOperator g w (V a) x := by
  funext x
  simp only [sourceWeightedOperator,complexDivergence,sourceFlux_finite_sum g w V hV,
    coordPartial_finite_sum _ (fun a ↦ hf a _),Finset.mul_sum]
  exact Finset.sum_comm

lemma sourceWeightedOperator_const_mul
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u)
    (hf : ∀ i, ContDiff ℝ ∞ (sourceFlux g w u i)) (c : ℂ) :
    sourceWeightedOperator g w (fun x ↦ c*u x) = fun x ↦ c*sourceWeightedOperator g w u x := by
  funext x
  simp only [sourceWeightedOperator,complexDivergence,sourceFlux_const_mul g w u hu,
    coordPartial_const_mul (hf _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma sourceWeightedOperator_real_projection
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (u : Coord → ℂ) (hu : Differentiable ℝ u)
    (hf : ∀ i, Differentiable ℝ (sourceFlux g w u i)) :
    sourceWeightedOperator g w (fun x ↦ ((u x).re:ℂ)) =
      fun x ↦ ((sourceWeightedOperator g w u x).re:ℂ) := by
  funext x
  simp [sourceWeightedOperator,complexDivergence,sourceFlux_real_projection g w u hu,
    coordPartial_real_projection _ (hf _),Complex.mul_re,← Complex.ofReal_inv]

theorem gaussianWaveField_source_residual
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (V : ι → Coord → ℂ) (hV : ∀ a, ContDiff ℝ ∞ (V a))
    (hf : ∀ a i, ContDiff ℝ ∞ (sourceFlux g w (V a) i))
    (coeff : ι × Fin 2 → ℝ) (lam : ℝ) :
    (fun x ↦ sourceWeightedOperator g w (fun z ↦ (gaussianWaveField V coeff z:ℂ)) x +
      (lam:ℂ)*(gaussianWaveField V coeff x:ℂ)) =
    fun x ↦ (gaussianWaveField
      (fun a x ↦ sourceWeightedOperator g w (V a) x+(lam:ℂ)*V a x) coeff x:ℂ) := by
  let Z : ι → Coord → ℂ := fun a x ↦ gaussianCoefficient coeff a*V a x
  have hZ (a : ι) : ContDiff ℝ ∞ (Z a) := contDiff_const.mul (hV a)
  have hZf (a : ι) (i : Fin 4) : ContDiff ℝ ∞ (sourceFlux g w (Z a) i) := by
    dsimp only [Z]
    rw [sourceFlux_const_mul g w _ (hV a)]
    exact contDiff_const.mul (hf a i)
  have hsum : ContDiff ℝ ∞ (fun x ↦ ∑ a, Z a x) := ContDiff.sum (fun a _ ↦ hZ a)
  have hsumf (i : Fin 4) : ContDiff ℝ ∞ (sourceFlux g w (fun x ↦ ∑ a, Z a x) i) := by
    rw [sourceFlux_finite_sum g w Z (fun a ↦ (hZ a).differentiable (by simp))]
    exact ContDiff.sum (fun a _ ↦ hZf a i)
  change (fun x ↦ sourceWeightedOperator g w (fun z ↦ (((∑ a, Z a z).re):ℂ)) x +
      (lam:ℂ)*(((∑ a, Z a x).re):ℂ)) = _
  rw [sourceWeightedOperator_real_projection g w _ (hsum.differentiable (by simp))
    (fun i ↦ (hsumf i).differentiable (by simp)),
    sourceWeightedOperator_finite_sum g w Z (fun a ↦ (hZ a).differentiable (by simp))
      (fun a i ↦ (hZf a i).differentiable (by simp))]
  funext x
  simp only [Z,sourceWeightedOperator_const_mul g w _ (hV _) (hf _),gaussianWaveField]
  apply Complex.ext <;> simp [Complex.mul_re,Finset.mul_sum,Finset.sum_add_distrib,mul_add,
    mul_left_comm,Finset.sum_sub_distrib,mul_sub]

end
end Yau.Geometry

end OAI
