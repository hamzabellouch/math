import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBConstruction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFrameBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPerturbedTransfer

namespace OAI

/-! Transfer for an actual scalar equation from the explicitly constructed WKB
frame. All frame equations and its nonzero Wronskian are discharged here. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_actual_transfer
    (R E : ℝ) (hRE : R≤ E) (chi : ℂ) (hchi : ‖chi‖=1)
    (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0<k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2=‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖≤‖p r‖^2)
    (hH : MonotoneOn (fun r => (spectralWKBPhase R chi p r).re) (Icc R E))
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q
      (spectralScalarField (-chi^2*(p r)^2) (q r)) r) :
    ∀ r ∈ Icc R E, spectralShellNorm (k r) (q r)≤
      (25/4 : ℝ)*spectralShellNorm (k R) (q R)*
        Real.exp ((spectralWKBPhase R chi p r).re-(spectralWKBPhase R chi p R).re+
          ∫ t in R..r, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2) := by
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
  have hHc : ContinuousOn H (Icc R E) :=
    Complex.continuous_re.comp_continuousOn (spectralWKBPhase_continuousOn R E hRE chi p hp)
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
  have hDb (t : ℝ) (ht : t ∈ Icc R E) :
      spectralShellNorm (k t) (D t)≤(5/2 : ℝ)*Real.exp (H t) := by
    exact spectralWKBState_shell_bound chi (p t) (v t) _ _ (k t) (hk0 t ht) (hkp t ht)
      (spectralWKBAmplitude_normalization R E hRE _ p v hp hv hp0 hpD
        (spectralWKBInitialAmplitude_normalization (p R) (hp0 R ⟨le_rfl,hRE⟩)) t ht)
      hchi.le (hsmall t ht)
  have hUb (t : ℝ) (ht : t ∈ Icc R E) :
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
  have ht := spectral_perturbed_transfer R E (5/2) 2 hRE (by norm_num) (by norm_num)
    D U q V e ((-2 : ℂ)*chi) k H hDc hUc hq he hk hHc hk0 hH
    (by rw [hnorm])
    (spectralWKBFrame_wronskian R E hRE chi p v hp hv hp0 hpD) hD hU hODE' hDb hUb
  simpa only [e,norm_neg,show (2 : ℝ)*(5/2)^2/2=25/4 by norm_num] using ht

end DefocusingNLS

end OAI
