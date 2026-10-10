import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDuhamelActionError

namespace OAI

/-! Error of the actual solution relative to its propagated initial WKB
coefficients, measured on the same growing action scale. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_initial_action_error
    (R E : ℝ) (hRE : R ≤ E) (chi : ℂ) (hchi : ‖chi‖ = 1)
    (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hH : MonotoneOn (fun r => (spectralWKBPhase R chi p r).re) (Icc R E))
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q
      (spectralScalarField (-chi^2*(p r)^2) (q r)) r) :
    let D := spectralWKBFrame R chi p v
    let U := spectralWKBFrame R (-chi) p v
    let W := (-2 : ℂ)*chi
    let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
    spectralShellNorm (k E)
      (q E-((spectralScalarWronskian (q R) (U R)/W) • D E+
        (spectralScalarWronskian (D R) (q R)/W) • U E)) ≤
      ((25/4 : ℝ)*spectralShellNorm (k R) (q R))*
        Real.exp ((spectralWKBPhase R chi p E).re+J)*J := by
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
  have hHc : ContinuousOn H (Icc R E) :=
    Complex.continuous_re.comp_continuousOn (spectralWKBPhase_continuousOn R E hRE chi p hp)
  have hzero : H R = 0 := by
    simp only [H,spectralWKBPhase,intervalIntegral.integral_same,mul_zero,Complex.zero_re]
  have ht := spectralWKB_actual_transfer R E hRE chi hchi p v w q k
    hp hv hw hq hk hk0 hkp hpD hvD hsmall hH hODE
  have hsol (t : ℝ) (htt : t ∈ Icc R E) : spectralShellNorm (k t) (q t) ≤
      ((25/4 : ℝ)*spectralShellNorm (k R) (q R))*
        Real.exp (H t+∫ s in R..t, (25/4 : ℝ)*‖e s‖/(k s)^2) := by
    have htt' := ht t htt
    change spectralShellNorm (k t) (q t) ≤
      ((25/4 : ℝ)*spectralShellNorm (k R) (q R))*
        Real.exp (H t-H R+∫ s in R..t,
          (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p s) (v s) (w s)‖/(k s)^2) at htt'
    rw [hzero,sub_zero] at htt'
    simpa only [e,norm_neg] using htt'
  have hker (t : ℝ) (htt : t ∈ Icc R E) :
      spectralShellNorm (k E) (spectralScalarTransferKernel D U ((-2 : ℂ)*chi) E t) ≤
        (25/4 : ℝ)/k t*Real.exp (H E-H t) := by
    have hh := spectralScalarTransferKernel_bound D U ((-2 : ℂ)*chi)
      (k E) (k t) (5/2) 2 (H E) (H t) E t (hk0 E ⟨hRE,le_rfl⟩).le
      (hk0 t htt) (by norm_num) (by norm_num) (by rw [hnorm])
      (hDb0 E ⟨hRE,le_rfl⟩) (hDb0 t htt) (hUb0 E ⟨hRE,le_rfl⟩) (hUb0 t htt)
    rw [abs_of_nonneg (sub_nonneg.mpr (hH htt ⟨hRE,le_rfl⟩ htt.2))] at hh
    convert hh using 1; dsimp only [H]; ring
  have herr := spectralScalarDuhamelIntegral_action_error R E (25/4)
    ((25/4 : ℝ)*spectralShellNorm (k R) (q R)) hRE (by norm_num)
    (mul_nonneg (by norm_num) (spectralShellNorm_nonneg _ (hk0 R ⟨le_rfl,hRE⟩).le _))
    D U q ((-2 : ℂ)*chi) e k H hDc hUc hq he hk hHc hk0 hker hsol
  have hrep := spectralScalarDuhamel_representation R E D U q V (fun t => e t*(q t).1)
    ((-2 : ℂ)*chi) hDc hUc hq (he.mul hq.fst)
    (norm_pos_iff.mp (by rw [hnorm]; norm_num))
    (spectralWKBFrame_wronskian R E hRE chi p v hp hv hp0 hpD) hD hU hODE' E ⟨hRE,le_rfl⟩
  have heq : q E-((spectralScalarWronskian (q R) (U R)/((-2 : ℂ)*chi)) • D E+
      (spectralScalarWronskian (D R) (q R)/((-2 : ℂ)*chi)) • U E) =
      spectralScalarDuhamelIntegral R D U ((-2 : ℂ)*chi) (fun t => e t*(q t).1) E := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hrep)
  rw [heq]
  simpa only [e,norm_neg,H] using herr

end DefocusingNLS

end OAI
