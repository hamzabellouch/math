import OAI.Analysis.CircleDomains.Sobolev.RealCoordinateLines
import OAI.Analysis.CircleDomains.Rigidity.AxialTargetDiskMeasure

namespace OAI

/-! The derivative of either target coordinate along a unit source axis
is bounded by the complex derivative norm. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complexCoordinateLine_contDiff (i : Fin 2) (y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (complexCoordinateLine i y) :=
  Complex.equivRealProdCLM.symm.contDiff.comp (realCoordinateLine_contDiff i y)

 theorem complexCoordinateLine_hasDerivAt (i : Fin 2) (y x : ℝ) :
    HasDerivAt (complexCoordinateLine i y) (if i = 0 then 1 else Complex.I) x := by
  fin_cases i
  · exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  · exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))

 theorem axial_complex_deriv (i : Fin 2) (y x : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableAt ℂ F (complexCoordinateLine i y x)) :
    HasDerivAt (fun t => F (complexCoordinateLine i y t))
      (deriv F (complexCoordinateLine i y x)*(if i = 0 then 1 else Complex.I)) x := by
  have h := (hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x
    (complexCoordinateLine_hasDerivAt i y x)
  change HasDerivAt (F ∘ complexCoordinateLine i y)
    ((if i = 0 then 1 else Complex.I)*deriv F (complexCoordinateLine i y x)) x at h
  simpa only [Function.comp_def,mul_comm] using h

 theorem axial_coordinate_deriv_le (i k : Fin 2) (y x : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableAt ℂ F (complexCoordinateLine i y x)) :
    |deriv (fun t => (complexPlaneCoordinates.symm (F (complexCoordinateLine i y t))) k) x| ≤
      ‖deriv F (complexCoordinateLine i y x)‖ := by
  have hd := axial_complex_deriv i y x hF
  have hn : ‖deriv F (complexCoordinateLine i y x)*(if i = 0 then 1 else Complex.I)‖ =
      ‖deriv F (complexCoordinateLine i y x)‖ := by
    split <;> simp
  fin_cases k
  · change |deriv (fun t => (F (complexCoordinateLine i y t)).re) x| ≤ _
    have he := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd).deriv
    change deriv (fun t => (F (complexCoordinateLine i y t)).re) x = _ at he
    rw [he]
    exact (Complex.abs_re_le_norm _).trans_eq hn
  · change |deriv (fun t => (F (complexCoordinateLine i y t)).im) x| ≤ _
    have he := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd).deriv
    change deriv (fun t => (F (complexCoordinateLine i y t)).im) x = _ at he
    rw [he]
    exact (Complex.abs_im_le_norm _).trans_eq hn

end CircleDomainRigidity

end

end OAI
