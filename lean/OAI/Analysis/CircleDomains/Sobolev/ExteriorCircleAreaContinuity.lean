import OAI.Analysis.CircleDomains.Sobolev.JordanSignedArea

namespace OAI

/-! The signed image-circle area varies continuously with the source
radius. Only holomorphy on the exterior open set is required. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_image_circle_deriv {F : ℂ → ℂ} {R a : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (ha : R < a) (t : ℝ) :
    deriv (fun t => F (unitCircleParam 0 a t)) t =
      deriv F (unitCircleParam 0 a t) *
        (unitCircleParam 0 a t * Complex.I * (2*Real.pi)) := by
  have hap : 0 < a := hR.trans ha
  have hz : unitCircleParam 0 a t ∈ {z : ℂ | R < ‖z‖} := by
    simpa only [mem_ofPred_eq, unitCircleParam, norm_circleMap_zero, abs_of_pos hap] using ha
  have hf := ((hF _ hz).differentiableAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)).hasDerivAt
  have hd := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (unitCircleParam_hasDerivAt a t)
  change deriv (F ∘ unitCircleParam 0 a) t = _
  rw [hd.deriv]
  change (unitCircleParam 0 a t * Complex.I * (2*Real.pi)) *
      deriv F (unitCircleParam 0 a t) = _
  exact mul_comm _ _

lemma exterior_circle_area_continuousOn {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) :
    ContinuousOn (fun a => signedCurveArea (fun t => F (unitCircleParam 0 a t))) (Ioi R) := by
  let : LocallyCompactSpace (Ioi R) := isOpen_Ioi.locallyCompactSpace
  let p : (Ioi R) × ℝ → ℂ := fun x => unitCircleParam 0 x.1.val x.2
  have hp : Continuous p := by
    dsimp only [p, unitCircleParam]
    exact (Real.circleMap.continuous (c := 0)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hloc (x : (Ioi R) × ℝ) : p x ∈ {z : ℂ | R < ‖z‖} := by
    simpa only [p, unitCircleParam, mem_ofPred_eq, norm_circleMap_zero,
      abs_of_pos (hR.trans x.1.property), mem_Ioi] using x.1.property
  have hf : Continuous (fun x => F (p x)) := hF.continuousOn.comp_continuous hp hloc
  have hd : Continuous (fun x => deriv F (p x)) :=
    (hF.deriv (isOpen_lt continuous_const continuous_norm)).continuousOn.comp_continuous hp hloc
  let v : (Ioi R) → ℝ → ℝ := fun a t => (F (p (a,t))).re *
    (deriv F (p (a,t)) * (p (a,t) * Complex.I * (2*Real.pi))).im
  have hv : Continuous v.uncurry := by
    exact (Complex.continuous_re.comp hf).mul
      (Complex.continuous_im.comp (hd.mul ((hp.mul_const Complex.I).mul_const (2*Real.pi))))
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hv (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hc using 1
  funext a
  change signedCurveArea (fun t => F (unitCircleParam 0 a.val t)) = _
  rw [signedCurveArea, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  change (F (unitCircleParam 0 a.val t)).re *
    (deriv (fun s => F (unitCircleParam 0 a.val s)) t).im = _
  rw [exterior_image_circle_deriv hR hF a.property]

end CircleDomainRigidity

end

end OAI
