import OAI.Analysis.CircleDomains.Probability.PhysicalLineFubini
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! Product and complex coordinates of the physical line families. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def realCoordinateLine (i : Fin 2) (y x : ℝ) : ℝ × ℝ :=
  if i = 0 then (x,y) else (y,x)

 theorem realCoordinateLine_contDiff (i : Fin 2) (y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (realCoordinateLine i y) := by
  unfold realCoordinateLine
  split <;> fun_prop

 theorem realCoordinateLine_physical (i : Fin 2) (y x : ℝ) :
    euclideanPlaneCoordinates (physicalCoordinateLine i y x) = realCoordinateLine i y x := by
  unfold physicalCoordinateLine realCoordinateLine
  split <;> exact euclideanPlaneCoordinates.apply_symm_apply _

 theorem realCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (fun p : ℝ × ℝ => realCoordinateLine i p.1 p.2)
      (volume.prod volume) volume := by
  have h := euclideanPlaneCoordinates_measurePreserving.comp
    (physicalCoordinatePlane_measurePreserving i)
  convert h using 1
  funext p
  exact (realCoordinateLine_physical i p.1 p.2).symm

 theorem ae_ae_realCoordinateLine {p : (ℝ × ℝ) → Prop}
    (hp : ∀ᵐ z ∂volume, p z) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ x ∂volume, p (realCoordinateLine i y x) :=
  Measure.ae_ae_of_ae_prod ((realCoordinatePlane_measurePreserving i).quasiMeasurePreserving.ae hp)

 theorem memLp_realCoordinateLine_ae {P : (ℝ × ℝ) → ℝ}
    (hP : Measurable P) (hL : MemLp P 2 volume) (i : Fin 2) :
    ∀ᵐ y ∂volume, MemLp (fun x => P (realCoordinateLine i y x)) 2 volume := by
  have hs := (realCoordinatePlane_measurePreserving i).integrable_comp_of_integrable hL.integrable_sq
  filter_upwards [hs.prod_right_ae] with y hy
  exact (memLp_two_iff_integrable_sq (hP.comp (realCoordinateLine_contDiff i y).continuous.measurable).aestronglyMeasurable).mpr hy

 theorem realCoordinateLine_deriv {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (y x : ℝ) :
    deriv (fun t => f (realCoordinateLine i y t)) x =
      fderiv ℝ f (realCoordinateLine i y x) (if i = 0 then (1,0) else (0,1)) := by
  fin_cases i
  · simpa [realCoordinateLine,Function.comp_def] using
      ((hf.differentiable_one (x,y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv
  · simpa [realCoordinateLine,Function.comp_def] using
      ((hf.differentiable_one (y,x)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))).deriv

 theorem realCoordinateLine_abs_deriv_le {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (y x : ℝ) :
    |deriv (fun t => f (realCoordinateLine i y t)) x| ≤ ‖fderiv ℝ f (realCoordinateLine i y x)‖ := by
  rw [realCoordinateLine_deriv hf,← Real.norm_eq_abs]
  apply ContinuousLinearMap.unit_le_opNorm
  split <;> simp

 def complexCoordinateLine (i : Fin 2) (y x : ℝ) : ℂ :=
  Complex.equivRealProdCLM.symm (realCoordinateLine i y x)

 def transverseCoordinate (i : Fin 2) (z : ℂ) : ℝ :=
  if i = 0 then z.im else z.re

 theorem complexCoordinateLine_transverse_le (i : Fin 2) (y x : ℝ) (c : ℂ) :
    |y-transverseCoordinate i c| ≤ ‖complexCoordinateLine i y x-c‖ := by
  fin_cases i
  · simpa [complexCoordinateLine,realCoordinateLine,transverseCoordinate] using
      Complex.abs_im_le_norm (complexCoordinateLine 0 y x-c)
  · simpa [complexCoordinateLine,realCoordinateLine,transverseCoordinate] using
      Complex.abs_re_le_norm (complexCoordinateLine 1 y x-c)

end CircleDomainRigidity

end

end OAI
