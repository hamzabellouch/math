import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundedFrameError

namespace OAI

/-! Terminal transfer error for the constructed WKB frame on an oscillatory
interval. The bounded real action is retained in the explicit constant. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_terminal_error
    (R E B J : ℝ) (hRE : R ≤ E) (chi : ℂ) (hchi : ‖chi‖ = 1)
    (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hphase : ∀ r ∈ Icc R E, |(spectralWKBPhase R chi p r).re| ≤ B)
    (hJ : (∫ r in R..E, ‖homogeneousSpectralWKBResidual (p r) (v r) (w r)‖/(k r)^2) ≤ J)
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q
      (spectralScalarField (-chi^2*(p r)^2) (q r)) r) :
    let D := spectralWKBFrame R chi p v
    let U := spectralWKBFrame R (-chi) p v
    let W := (-2 : ℂ)*chi
    let C := (5/2 : ℝ)*Real.exp B
    spectralShellNorm (k R)
      (q R - ((spectralScalarWronskian (q E) (U E)/W) • D R +
        (spectralScalarWronskian (D E) (q E)/W) • U R)) ≤
      (2*(C^2)^2*Real.exp (C^2*J)*J)*spectralShellNorm (k E) (q E) := by
  dsimp only
  have hp0 (r : ℝ) (hr : r ∈ Icc R E) : p r≠0 := by
    apply norm_pos_iff.mp
    rw [← hkp r hr]
    exact sq_pos_of_pos (hk0 r hr)
  let e := fun r => -homogeneousSpectralWKBResidual (p r) (v r) (w r)
  let V := fun r => -(chi^2*(p r)^2-e r)
  let D := spectralWKBFrame R chi p v
  let U := spectralWKBFrame R (-chi) p v
  let H := fun r => (spectralWKBPhase R chi p r).re
  have he : ContinuousOn e (Icc R E) := by
    exact ((continuousOn_const.mul ((hv.div hp hp0).pow 2)).sub
      (hw.div (continuousOn_const.mul hp)
        (fun r hr => mul_ne_zero (by norm_num) (hp0 r hr)))).neg
  have hDc := spectralWKBFrame_continuousOn R E hRE chi p v hp hv hp0
  have hUc := spectralWKBFrame_continuousOn R E hRE (-chi) p v hp hv hp0
  have hD (t : ℝ) (ht : t ∈ Ioo R E) : HasDerivAt D (spectralScalarField (V t) (D t)) t := by
    simpa only [V,e,sub_neg_eq_add] using
      spectralWKBFrame_hasDerivAt R E chi p v hp hv hp0 (w t) t ht (hpD t ht) (hvD t ht)
  have hU (t : ℝ) (ht : t ∈ Ioo R E) : HasDerivAt U (spectralScalarField (V t) (U t)) t := by
    have hh := spectralWKBFrame_hasDerivAt R E (-chi) p v hp hv hp0 (w t) t ht (hpD t ht) (hvD t ht)
    simpa only [V,e,sub_neg_eq_add,neg_sq] using hh
  have hODE' (t : ℝ) (ht : t ∈ Ioo R E) :
      HasDerivAt q (spectralScalarField (V t) (q t)+(0,e t*(q t).1)) t := by
    apply (hODE t ht).congr_deriv
    apply Prod.ext
    · simp only [spectralScalarField,Prod.fst_add,add_zero]
    · dsimp only [spectralScalarField,Prod.snd_add,V]
      ring
  have hnorm : ‖(-2 : ℂ)*chi‖=2 := by rw [norm_mul,hchi,mul_one]; norm_num
  have hDb0 (t : ℝ) (ht : t ∈ Icc R E) :
      spectralShellNorm (k t) (D t)≤(5/2 : ℝ)*Real.exp (H t) := by
    exact spectralWKBState_shell_bound chi (p t) (v t) _ _ (k t) (hk0 t ht) (hkp t ht)
      (spectralWKBAmplitude_normalization R E hRE _ p v hp hv hp0 hpD
        (spectralWKBInitialAmplitude_normalization (p R) (hp0 R ⟨le_rfl,hRE⟩)) t ht)
      hchi.le (hsmall t ht)
  have hUb0 (t : ℝ) (ht : t ∈ Icc R E) :
      spectralShellNorm (k t) (U t)≤(5/2 : ℝ)*Real.exp (-H t) := by
    have hh := spectralWKBState_shell_bound (-chi) (p t) (v t)
      (spectralWKBAmplitude R (spectralWKBInitialAmplitude (p R)) p v t)
      (spectralWKBPhase R (-chi) p t) (k t) (hk0 t ht) (hkp t ht)
      (spectralWKBAmplitude_normalization R E hRE _ p v hp hv hp0 hpD
        (spectralWKBInitialAmplitude_normalization (p R) (hp0 R ⟨le_rfl,hRE⟩)) t ht)
      (by simpa only [norm_neg] using hchi.le) (hsmall t ht)
    have hsre : (spectralWKBPhase R (-chi) p t).re= -H t := by
      dsimp only [spectralWKBPhase,H]
      rw [neg_mul,Complex.neg_re]
    change spectralShellNorm (k t) (U t)≤(5/2 : ℝ)*Real.exp ((spectralWKBPhase R (-chi) p t).re) at hh
    rw [hsre] at hh
    exact hh
  let C := (5/2 : ℝ)*Real.exp B
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hDb (t : ℝ) (ht : t ∈ Icc R E) : spectralShellNorm (k t) (D t) ≤ C := by
    apply (hDb0 t ht).trans
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((le_abs_self (H t)).trans (hphase t ht)))
      (by norm_num)
  have hUb (t : ℝ) (ht : t ∈ Icc R E) : spectralShellNorm (k t) (U t) ≤ C := by
    apply (hUb0 t ht).trans
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((neg_le_abs (H t)).trans (hphase t ht)))
      (by norm_num)
  have hVc : ContinuousOn V (Icc R E) :=
    ((continuousOn_const.mul (hp.pow 2)).sub he).neg
  have herr := spectral_bounded_frame_terminal_error R E C 2 J hRE hC (by norm_num)
    D U q V e ((-2 : ℂ)*chi) k hDc hUc hq hVc he hk hk0 (by rw [hnorm])
    (spectralWKBFrame_wronskian R E hRE chi p v hp hv hp0 hpD) hD hU hODE' hDb hUb
    (by simpa only [e,norm_neg] using hJ)
  simpa only [C,D,U,show 2*C^2/2=C^2 by ring] using herr

end DefocusingNLS

end OAI
