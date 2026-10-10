import OAI.Analysis.CircleDomains.Sobolev.RealGradientTransport
import OAI.Analysis.CircleDomains.Rigidity.SelectedTraceBound
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Coordinate lines in the actual Euclidean Sobolev plane. Their
one-dimensional derivatives and total energies are the physical partials. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def physicalCoordinateLine (i : Fin 2) (y x : ℝ) : EuclideanPlane :=
  if i = 0 then euclideanPlaneCoordinates.symm (x,y)
  else euclideanPlaneCoordinates.symm (y,x)

 theorem physicalCoordinateLine_contDiff (i : Fin 2) (y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCoordinateLine i y) := by
  unfold physicalCoordinateLine
  split <;> fun_prop

 theorem physicalCoordinateLine_deriv {f : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) (y x : ℝ) :
    deriv (fun t => f (physicalCoordinateLine i y t)) x =
      fderiv ℝ f (physicalCoordinateLine i y x) (EuclideanSpace.single i 1) := by
  have h0 := (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h1 := (hasDerivAt_const x y).prodMk (hasDerivAt_id x)
  have he0 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt x h0
  have he1 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt x h1
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,
      show euclideanPlaneCoordinates.symm (1,0) = EuclideanSpace.single (0 : Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 0] using
      ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt x he0).deriv
  · simpa [physicalCoordinateLine,Function.comp_def,
      show euclideanPlaneCoordinates.symm (0,1) = EuclideanSpace.single (1 : Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 1] using
      ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt x he1).deriv

 theorem physicalCoordinateLine_energy_integrable {f : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2)
    (hi : Integrable (fun z => (fderiv ℝ f z (EuclideanSpace.single i 1))^2) volume) :
    Integrable (fun p : ℝ × ℝ => deriv (fun t => f (physicalCoordinateLine i p.1 t)) p.2^2)
      (volume.prod volume) := by
  simp only [physicalCoordinateLine_deriv hf]
  have hm := euclideanPlaneCoordinates_symm_measurePreserving.integrable_comp_of_integrable hi
  rw [Measure.volume_eq_prod] at hm
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,Prod.swap] using hm.swap
  · simpa [physicalCoordinateLine,
      Function.comp_def] using hm

 theorem physicalCoordinateLine_energy_eq {f : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    (∫ p : ℝ × ℝ, deriv (fun t => f (physicalCoordinateLine i p.1 t)) p.2^2
      ∂(volume.prod volume)) =
    ∫ z, (fderiv ℝ f z (EuclideanSpace.single i 1))^2 := by
  simp only [physicalCoordinateLine_deriv hf]
  have hm := euclideanPlaneCoordinates_symm_measurePreserving.integral_comp
    euclideanPlaneCoordinates.symm.toHomeomorph.measurableEmbedding
    (fun z => (fderiv ℝ f z (EuclideanSpace.single i 1))^2)
  rw [Measure.volume_eq_prod] at hm
  fin_cases i
  · change (∫ p : ℝ × ℝ, (fderiv ℝ f (euclideanPlaneCoordinates.symm p.swap)
      (EuclideanSpace.single 0 1))^2 ∂(volume.prod volume)) = _
    exact (integral_prod_swap _).trans hm
  · exact hm

 theorem physicalCoordinateLine_coordinate (i : Fin 2) (y x : ℝ) :
    physicalCoordinateLine i y x i = x := by
  fin_cases i
  · change (euclideanPlaneCoordinates.symm (x,y)) 0 = x
    exact congrArg Prod.fst (euclideanPlaneCoordinates.apply_symm_apply (x,y))
  · change (euclideanPlaneCoordinates.symm (y,x)) 1 = x
    exact congrArg Prod.snd (euclideanPlaneCoordinates.apply_symm_apply (y,x))

 theorem physicalCoordinateLine_norm_le (i : Fin 2) (y x : ℝ) :
    ‖physicalCoordinateLine i y x‖ ≤ |x|+|y| := by
  have he (a b : ℝ) : euclideanPlaneCoordinates.symm (a,b) = planePair a b := by
    apply euclideanPlaneCoordinates.injective
    simp only [euclideanPlaneCoordinates_apply,planePair_zero,planePair_one,
      ContinuousLinearEquiv.apply_symm_apply]
  fin_cases i
  · simpa [physicalCoordinateLine,he] using planePair_norm_le x y
  · simpa [physicalCoordinateLine,he,
      add_comm] using planePair_norm_le y x

end CircleDomainRigidity

end

end OAI
