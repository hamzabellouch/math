import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBReflectedError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBInitialCone

namespace OAI

/-! The growing-coefficient and residual criteria give a Robin cone at
the physical inner endpoint after reflection. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_reflected_cone
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
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (-(p r)^2) (q r)) r)
    (hN : 0 < spectralShellNorm (k E) (q E))
    (ha : spectralShellNorm (k E) (q E)/8 ≤
      ‖spectralScalarWronskian ((Complex.sqrt (p E))⁻¹,
        (p E-v E/(2*p E))*(Complex.sqrt (p E))⁻¹) (q E)/(-2)‖)
    (herror :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
      let H := (∫ t in R..E, p t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ 1/64) :
    (q R).1 ≠ 0 ∧ ‖(q R).2+(p R+v R/(2*p R))*(q R).1‖ ≤
      (1/2 : ℝ)*‖p R‖*‖(q R).1‖ := by
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
  have hNR : 0 < spectralShellNorm (K R) (Q R) := by
    simpa only [K,Q,j,spectralScalarReflect_norm,add_sub_cancel_left] using hN
  have haR : spectralShellNorm (K R) (Q R)/8 ≤
      ‖spectralScalarWronskian (Q R) (spectralWKBFrame R (-1) P V R)/(-2)‖ := by
    have he : spectralScalarWronskian (Q R) (spectralWKBFrame R (-1) P V R) =
        spectralScalarWronskian ((Complex.sqrt (p E))⁻¹,
          (p E-v E/(2*p E))*(Complex.sqrt (p E))⁻¹) (q E) := by
      rw [spectralWKBFrame_initial]
      simp only [Q,spectralScalarReflect,P,V,j,add_sub_cancel_left,spectralWKBState,
        spectralWKBValue,Complex.exp_zero,mul_one,spectralWKBInitialAmplitude,
        homogeneousSpectralWKBLog,spectralScalarWronskian]
      ring
    rw [he]
    simpa only [K,Q,j,spectralScalarReflect_norm,add_sub_cancel_left] using ha
  have herr :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (P t) (V t) (W t)‖/(K t)^2
      let H := (spectralWKBPhase R 1 P E).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ 1/64 := by
    dsimp only [P,V,W,K,j]
    rw [spectralWKB_reflected_residual_integral,spectralWKB_reflected_phase]
    exact herror
  have hc := spectralWKB_initial_cone R E hRE P V W Q K
    hPc hVc hWc hQc hKc (fun t ht => hk0 (j t) (hj t ht))
    (fun t ht => hkp (j t) (hj t ht)) hPD hVD
    (fun t ht => by simpa only [V,norm_neg] using hsmall (j t) (hj t ht)) hmono (fun t ht => by simpa only [one_pow,neg_one_mul] using hQODE t ht) hNR haR herr
  have hres : (Q E).2-homogeneousSpectralWKBLog 1 (P E) (V E)*(Q E).1 =
      -((q R).2+(p R+v R/(2*p R))*(q R).1) := by
    simp only [Q,spectralScalarReflect,P,V,j,add_sub_cancel_right,homogeneousSpectralWKBLog]
    ring
  rw [hres,norm_neg] at hc
  simpa only [Q,spectralScalarReflect,P,j,add_sub_cancel_right] using hc

theorem spectralWKB_reflected_relative_bounds
    (eps : ℝ) (heps : 0 < eps) (R E : ℝ) (hRE : R ≤ E)
    (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hpositive : ∀ r ∈ Icc R E, 0 ≤ (p r).re)
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (-(p r)^2) (q r)) r)
    (hN : 0 < spectralShellNorm (k E) (q E))
    (ha : spectralShellNorm (k E) (q E)/8 ≤
      ‖spectralScalarWronskian ((Complex.sqrt (p E))⁻¹,
        (p E-v E/(2*p E))*(Complex.sqrt (p E))⁻¹) (q E)/(-2)‖)
    (herror :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
      let H := (∫ t in R..E, p t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ min (1/16) (eps/40)) :
    ((q R).1 ≠ 0 ∧ ‖(q R).2+(p R+v R/(2*p R))*(q R).1‖ ≤
      eps*‖p R‖*‖(q R).1‖) ∧
      (1/16 : ℝ)*Real.exp ((∫ t in R..E, p t).re)*
        spectralShellNorm (k E) (q E) ≤ (k R)*‖(q R).1‖ := by
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
  have hNR : 0 < spectralShellNorm (K R) (Q R) := by
    simpa only [K,Q,j,spectralScalarReflect_norm,add_sub_cancel_left] using hN
  have haR : spectralShellNorm (K R) (Q R)/8 ≤
      ‖spectralScalarWronskian (Q R) (spectralWKBFrame R (-1) P V R)/(-2)‖ := by
    have he : spectralScalarWronskian (Q R) (spectralWKBFrame R (-1) P V R) =
        spectralScalarWronskian ((Complex.sqrt (p E))⁻¹,
          (p E-v E/(2*p E))*(Complex.sqrt (p E))⁻¹) (q E) := by
      rw [spectralWKBFrame_initial]
      simp only [Q,spectralScalarReflect,P,V,j,add_sub_cancel_left,spectralWKBState,
        spectralWKBValue,Complex.exp_zero,mul_one,spectralWKBInitialAmplitude,
        homogeneousSpectralWKBLog,spectralScalarWronskian]
      ring
    rw [he]
    simpa only [K,Q,j,spectralScalarReflect_norm,add_sub_cancel_left] using ha
  have herr :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (P t) (V t) (W t)‖/(K t)^2
      let H := (spectralWKBPhase R 1 P E).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ min (1/16) (eps/40) := by
    dsimp only [P,V,W,K,j]
    rw [spectralWKB_reflected_residual_integral,spectralWKB_reflected_phase]
    exact herror
  have hc := spectralWKB_initial_relative_bounds eps heps R E hRE P V W Q K
    hPc hVc hWc hQc hKc (fun t ht => hk0 (j t) (hj t ht))
    (fun t ht => hkp (j t) (hj t ht)) hPD hVD
    (fun t ht => by simpa only [V,norm_neg] using hsmall (j t) (hj t ht)) hmono (fun t ht => by simpa only [one_pow,neg_one_mul] using hQODE t ht) hNR haR herr
  have hres : (Q E).2-homogeneousSpectralWKBLog 1 (P E) (V E)*(Q E).1 =
      -((q R).2+(p R+v R/(2*p R))*(q R).1) := by
    simp only [Q,spectralScalarReflect,P,V,j,add_sub_cancel_right,homogeneousSpectralWKBLog]
    ring
  rw [hres,norm_neg] at hc
  simpa only [Q,spectralScalarReflect,P,K,j,add_sub_cancel_right,add_sub_cancel_left,
    spectralScalarReflect_norm,spectralWKB_reflected_phase,spectralShellNorm,norm_neg] using hc

theorem spectralWKB_reflected_relative_cone
    (eps : ℝ) (heps : 0 < eps) (R E : ℝ) (hRE : R ≤ E)
    (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hpositive : ∀ r ∈ Icc R E, 0 ≤ (p r).re)
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (-(p r)^2) (q r)) r)
    (hN : 0 < spectralShellNorm (k E) (q E))
    (ha : spectralShellNorm (k E) (q E)/8 ≤
      ‖spectralScalarWronskian ((Complex.sqrt (p E))⁻¹,
        (p E-v E/(2*p E))*(Complex.sqrt (p E))⁻¹) (q E)/(-2)‖)
    (herror :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
      let H := (∫ t in R..E, p t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ min (1/16) (eps/40)) :
    (q R).1 ≠ 0 ∧ ‖(q R).2+(p R+v R/(2*p R))*(q R).1‖ ≤
      eps*‖p R‖*‖(q R).1‖ := by
  exact (spectralWKB_reflected_relative_bounds eps heps R E hRE p v w q k hp hv hw hq hk hk0
    hkp hpD hvD hsmall hpositive hODE hN ha herror).1

end DefocusingNLS

end OAI
