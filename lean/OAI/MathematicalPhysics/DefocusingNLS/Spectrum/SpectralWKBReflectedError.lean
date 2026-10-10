import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBInitialError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReflection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseOrder

namespace OAI

/-! Propagate the growing WKB coefficient from the turning edge toward a
fixed inner radius by reflecting the actual Cauchy equation. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_reflected_action_error
    (R E : ℝ) (hRE : R ≤ E)
    (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hpositive : ∀ r ∈ Icc R E, 0 ≤ (p r).re)
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (-(p r)^2) (q r)) r) :
    let P := fun t => p (R+E-t)
    let V := fun t => -v (R+E-t)
    let Q := spectralScalarReflect R E q
    let D := spectralWKBFrame R 1 P V
    let U := spectralWKBFrame R (-1) P V
    let J := ∫ t in R..E, (25/4 : ℝ)*
      ‖homogeneousSpectralWKBResidual (P t) (V t) (w (R+E-t))‖/(k (R+E-t))^2
    spectralShellNorm (k R)
      (Q E-((spectralScalarWronskian (Q R) (U R)/(-2)) • D E+
        (spectralScalarWronskian (D R) (Q R)/(-2)) • U E)) ≤
      ((25/4 : ℝ)*spectralShellNorm (k E) (q E))*
        Real.exp ((spectralWKBPhase R 1 P E).re+J)*J := by
  dsimp only
  let j := fun t : ℝ => R+E-t
  have hj (t : ℝ) (ht : t ∈ Icc R E) : j t ∈ Icc R E := by
    dsimp only [j]
    constructor <;> linarith [ht.1,ht.2]
  have hjo (t : ℝ) (ht : t ∈ Ioo R E) : j t ∈ Ioo R E := by
    dsimp only [j]
    constructor <;> linarith [ht.1,ht.2]
  have hjc : Continuous j := continuous_const.sub continuous_id
  let P := fun t => p (j t)
  let V := fun t => -v (j t)
  let W := fun t => w (j t)
  let K := fun t => k (j t)
  let Q := spectralScalarReflect R E q
  have hPc : ContinuousOn P (Icc R E) := hp.comp hjc.continuousOn hj
  have hVc : ContinuousOn V (Icc R E) := (hv.comp hjc.continuousOn hj).neg
  have hWc : ContinuousOn W (Icc R E) := hw.comp hjc.continuousOn hj
  have hKc : ContinuousOn K (Icc R E) := hk.comp hjc.continuousOn hj
  have hQc : ContinuousOn Q (Icc R E) :=
    ((hq.comp hjc.continuousOn hj).fst).prodMk ((hq.comp hjc.continuousOn hj).snd.neg)
  have hPD (t : ℝ) (ht : t ∈ Ioo R E) : HasDerivAt P (V t) t := by
    have hh := (hpD (j t) (hjo t ht)).scomp t ((hasDerivAt_id t).const_sub (R+E))
    simpa only [P,V,j,Function.comp_def,neg_one_smul] using hh
  have hVD (t : ℝ) (ht : t ∈ Ioo R E) : HasDerivAt V (W t) t := by
    have hh := ((hvD (j t) (hjo t ht)).scomp t ((hasDerivAt_id t).const_sub (R+E))).neg
    change HasDerivAt (fun x => -v (j x)) (-((-1 : ℝ) • w (j t))) t at hh
    simpa only [V,W,j,neg_one_smul,neg_neg] using hh
  have hQODE (t : ℝ) (ht : t ∈ Ioo R E) :
      HasDerivAt Q (spectralScalarField (-(1 : ℂ)^2*(P t)^2) (Q t)) t := by
    simpa only [one_pow,neg_one_mul] using
      spectralScalarReflect_hasDerivAt R E t q (-(P t)^2) (hODE (j t) (hjo t ht))
  have hmono : MonotoneOn (fun t => (spectralWKBPhase R 1 P t).re) (Icc R E) :=
    spectralWKBPhase_monotone R E hRE 1 P hPc (fun t ht => by
      simpa only [one_mul] using hpositive (j t) (hj t ⟨ht.1.le,ht.2.le⟩))
  have hh := spectralWKB_initial_action_error R E hRE 1 (by norm_num) P V W Q K
    hPc hVc hWc hQc hKc (fun t ht => hk0 (j t) (hj t ht))
    (fun t ht => hkp (j t) (hj t ht)) hPD hVD
    (fun t ht => by simpa only [V,norm_neg] using hsmall (j t) (hj t ht)) hmono hQODE
  simpa only [P,V,W,K,Q,j,neg_mul,mul_one,one_mul,spectralScalarReflect_norm,
    add_sub_cancel_left,add_sub_cancel_right] using hh

theorem spectralWKB_reflected_residual_integral (R E : ℝ)
    (p v w : ℝ → ℂ) (k : ℝ → ℝ) :
    (∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual
      (p (R+E-t)) (-v (R+E-t)) (w (R+E-t))‖/(k (R+E-t))^2) =
    ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2 := by
  simpa only [homogeneousSpectralWKBResidual,neg_div,neg_sq,
    add_sub_cancel_left,add_sub_cancel_right] using
    intervalIntegral.integral_comp_sub_left
      (fun t => (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2)
      (a := R) (b := E) (R+E)

theorem spectralWKB_reflected_phase (R E : ℝ) (p : ℝ → ℂ) :
    spectralWKBPhase R 1 (fun t => p (R+E-t)) E = ∫ t in R..E, p t := by
  simp only [spectralWKBPhase,one_mul]
  rw [intervalIntegral.integral_comp_sub_left]
  simp only [add_sub_cancel_left,add_sub_cancel_right]

end DefocusingNLS

end OAI
