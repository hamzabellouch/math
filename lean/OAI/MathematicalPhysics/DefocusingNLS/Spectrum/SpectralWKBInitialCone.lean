import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBInitialError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGrowingBranchCone
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFrameValue

namespace OAI

/-! The actual solution enters a strict Robin cone when its initial growing
coefficient has the Airy margin and the residual and reflected branch are small. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_initial_cone
    (R E : ℝ) (hRE : R ≤ E) (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hH : MonotoneOn (fun r => (spectralWKBPhase R 1 p r).re) (Icc R E))
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (-(p r)^2) (q r)) r)
    (hN : 0 < spectralShellNorm (k R) (q R))
    (ha : spectralShellNorm (k R) (q R)/8 ≤
      ‖spectralScalarWronskian (q R) (spectralWKBFrame R (-1) p v R)/(-2)‖)
    (hsmallError :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
      let H := (spectralWKBPhase R 1 p E).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ 1/64) :
    (q E).1 ≠ 0 ∧
      ‖(q E).2-homogeneousSpectralWKBLog 1 (p E) (v E)*(q E).1‖ ≤
        (1/2 : ℝ)*‖p E‖*‖(q E).1‖ := by
  let D := spectralWKBFrame R 1 p v
  let U := spectralWKBFrame R (-1) p v
  let H := (spectralWKBPhase R 1 p E).re
  let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
  let N := spectralShellNorm (k R) (q R)
  let a := spectralScalarWronskian (q R) (U R)/(-2)
  let b := spectralScalarWronskian (D R) (q R)/(-2)
  have hRI : R ∈ Icc R E := ⟨le_rfl,hRE⟩
  have hEI : E ∈ Icc R E := ⟨hRE,le_rfl⟩
  have hpn (r : ℝ) (hr : r ∈ Icc R E) : p r ≠ 0 := by
    apply norm_pos_iff.mp
    rw [← hkp r hr]
    exact sq_pos_of_pos (hk0 r hr)
  have hDR : spectralShellNorm (k R) (D R) ≤ 5/2 := by
    dsimp only [D]
    rw [spectralWKBFrame_initial]
    simpa only [Complex.zero_re,Real.exp_zero,mul_one] using
      spectralWKBState_shell_bound 1 (p R) (v R) (spectralWKBInitialAmplitude (p R)) 0
        (k R) (hk0 R hRI) (hkp R hRI)
        (spectralWKBInitialAmplitude_normalization (p R) (hpn R hRI)) (by norm_num) (hsmall R hRI)
  have hUE : spectralShellNorm (k E) (U E) ≤ (5/2 : ℝ)*Real.exp (-H) := by
    have hb := spectralWKBState_shell_bound (-1) (p E) (v E)
      (spectralWKBAmplitude R (spectralWKBInitialAmplitude (p R)) p v E)
      (spectralWKBPhase R (-1) p E) (k E) (hk0 E hEI) (hkp E hEI)
      (spectralWKBAmplitude_normalization R E hRE _ p v hp hv hpn hpD
        (spectralWKBInitialAmplitude_normalization (p R) (hpn R hRI)) E hEI)
      (by norm_num) (hsmall E hEI)
    simpa only [U,spectralWKBFrame,spectralWKBPhase,H,neg_mul,one_mul,Complex.neg_re] using hb
  have hb : ‖b‖ ≤ (5/2 : ℝ)/2*N := by
    dsimp only [b]
    rw [norm_div]
    norm_num only [norm_neg,Complex.norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hw := spectralScalarWronskian_shell_bound (k R) (hk0 R hRI) (D R) (q R)
    nlinarith [mul_le_mul_of_nonneg_right hDR hN.le]
  have herr := spectralWKB_initial_action_error R E hRE 1 (by norm_num)
    p v w q k hp hv hw hq hk hk0 hkp hpD hvD hsmall hH
    (fun t ht => by simpa only [one_pow,neg_one_mul] using hODE t ht)
  dsimp only at herr
  simp only [mul_one] at herr
  have he : spectralShellNorm (k E) (q E-(a • D E+b • U E)) ≤
      ((25/4 : ℝ)*Real.exp J*J)*Real.exp H*N := by
    change spectralShellNorm (k E) (q E-(a • D E+b • U E)) ≤
      ((25/4 : ℝ)*N)*Real.exp (H+J)*J at herr
    rw [Real.exp_add] at herr
    convert herr using 1; ring
  have hclose := spectralGrowingBranch_error (k E) (5/2) H N
    ((25/4 : ℝ)*Real.exp J*J) (hk0 E hEI) (by norm_num) hN.le a b (D E) (U E) (q E) hUE hb he
  have hvalue := spectralWKBFrame_value_norm R E hRE 1 p v hp hv hpn hpD (k E) E
    (hk0 E hEI) (hkp E hEI) hEI
  have hlog := spectralWKB_log_bound 1 (p E) (v E) (hpn E hEI) (by norm_num) (hsmall E hEI)
  have hc := spectralGrowingBranch_cone (k E) H N
    ((25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H)) (hk0 E hEI) hN
    hsmallError a (homogeneousSpectralWKBLog 1 (p E) (v E)) (D E) (q E)
    (by rfl) hvalue (by simpa only [hkp E hEI] using hlog) ha (by norm_num only at hclose ⊢; exact hclose)
  simpa only [hkp E hEI] using hc

theorem spectralWKB_initial_relative_bounds
    (eps : ℝ) (heps : 0 < eps) (R E : ℝ) (hRE : R ≤ E) (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hH : MonotoneOn (fun r => (spectralWKBPhase R 1 p r).re) (Icc R E))
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (-(p r)^2) (q r)) r)
    (hN : 0 < spectralShellNorm (k R) (q R))
    (ha : spectralShellNorm (k R) (q R)/8 ≤
      ‖spectralScalarWronskian (q R) (spectralWKBFrame R (-1) p v R)/(-2)‖)
    (hsmallError :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
      let H := (spectralWKBPhase R 1 p E).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ min (1/16) (eps/40)) :
    ((q E).1 ≠ 0 ∧
      ‖(q E).2-homogeneousSpectralWKBLog 1 (p E) (v E)*(q E).1‖ ≤
        eps*‖p E‖*‖(q E).1‖) ∧
      (1/16 : ℝ)*Real.exp ((spectralWKBPhase R 1 p E).re)*
        spectralShellNorm (k R) (q R) ≤ (k E)*‖(q E).1‖ := by
  let D := spectralWKBFrame R 1 p v
  let U := spectralWKBFrame R (-1) p v
  let H := (spectralWKBPhase R 1 p E).re
  let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
  let N := spectralShellNorm (k R) (q R)
  let a := spectralScalarWronskian (q R) (U R)/(-2)
  let b := spectralScalarWronskian (D R) (q R)/(-2)
  have hRI : R ∈ Icc R E := ⟨le_rfl,hRE⟩
  have hEI : E ∈ Icc R E := ⟨hRE,le_rfl⟩
  have hpn (r : ℝ) (hr : r ∈ Icc R E) : p r ≠ 0 := by
    apply norm_pos_iff.mp
    rw [← hkp r hr]
    exact sq_pos_of_pos (hk0 r hr)
  have hDR : spectralShellNorm (k R) (D R) ≤ 5/2 := by
    dsimp only [D]
    rw [spectralWKBFrame_initial]
    simpa only [Complex.zero_re,Real.exp_zero,mul_one] using
      spectralWKBState_shell_bound 1 (p R) (v R) (spectralWKBInitialAmplitude (p R)) 0
        (k R) (hk0 R hRI) (hkp R hRI)
        (spectralWKBInitialAmplitude_normalization (p R) (hpn R hRI)) (by norm_num) (hsmall R hRI)
  have hUE : spectralShellNorm (k E) (U E) ≤ (5/2 : ℝ)*Real.exp (-H) := by
    have hb := spectralWKBState_shell_bound (-1) (p E) (v E)
      (spectralWKBAmplitude R (spectralWKBInitialAmplitude (p R)) p v E)
      (spectralWKBPhase R (-1) p E) (k E) (hk0 E hEI) (hkp E hEI)
      (spectralWKBAmplitude_normalization R E hRE _ p v hp hv hpn hpD
        (spectralWKBInitialAmplitude_normalization (p R) (hpn R hRI)) E hEI)
      (by norm_num) (hsmall E hEI)
    simpa only [U,spectralWKBFrame,spectralWKBPhase,H,neg_mul,one_mul,Complex.neg_re] using hb
  have hb : ‖b‖ ≤ (5/2 : ℝ)/2*N := by
    dsimp only [b]
    rw [norm_div]
    norm_num only [norm_neg,Complex.norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hw := spectralScalarWronskian_shell_bound (k R) (hk0 R hRI) (D R) (q R)
    nlinarith [mul_le_mul_of_nonneg_right hDR hN.le]
  have herr := spectralWKB_initial_action_error R E hRE 1 (by norm_num)
    p v w q k hp hv hw hq hk hk0 hkp hpD hvD hsmall hH
    (fun t ht => by simpa only [one_pow,neg_one_mul] using hODE t ht)
  dsimp only at herr
  simp only [mul_one] at herr
  have he : spectralShellNorm (k E) (q E-(a • D E+b • U E)) ≤
      ((25/4 : ℝ)*Real.exp J*J)*Real.exp H*N := by
    change spectralShellNorm (k E) (q E-(a • D E+b • U E)) ≤
      ((25/4 : ℝ)*N)*Real.exp (H+J)*J at herr
    rw [Real.exp_add] at herr
    convert herr using 1; ring
  have hclose := spectralGrowingBranch_error (k E) (5/2) H N
    ((25/4 : ℝ)*Real.exp J*J) (hk0 E hEI) (by norm_num) hN.le a b (D E) (U E) (q E) hUE hb he
  have hvalue := spectralWKBFrame_value_norm R E hRE 1 p v hp hv hpn hpD (k E) E
    (hk0 E hEI) (hkp E hEI) hEI
  have hlog := spectralWKB_log_bound 1 (p E) (v E) (hpn E hEI) (by norm_num) (hsmall E hEI)
  have hc := spectralGrowingBranch_relative_cone (k E) H N
    ((25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H)) (hk0 E hEI) hN eps heps
    hsmallError a (homogeneousSpectralWKBLog 1 (p E) (v E)) (D E) (q E)
    (by rfl) hvalue (by simpa only [hkp E hEI] using hlog) ha (by norm_num only at hclose ⊢; exact hclose)
  refine ⟨?_,?_⟩
  · simpa only [hkp E hEI] using hc
  · exact spectralGrowingBranch_value_lower (k E) H N
      ((25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H)) (hk0 E hEI) hN.le
      ((le_min_iff.mp hsmallError).1) a (D E) (q E) hvalue ha
      (by norm_num only at hclose ⊢; exact hclose)

theorem spectralWKB_initial_relative_cone
    (eps : ℝ) (heps : 0 < eps) (R E : ℝ) (hRE : R ≤ E) (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hH : MonotoneOn (fun r => (spectralWKBPhase R 1 p r).re) (Icc R E))
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (-(p r)^2) (q r)) r)
    (hN : 0 < spectralShellNorm (k R) (q R))
    (ha : spectralShellNorm (k R) (q R)/8 ≤
      ‖spectralScalarWronskian (q R) (spectralWKBFrame R (-1) p v R)/(-2)‖)
    (hsmallError :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
      let H := (spectralWKBPhase R 1 p E).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ min (1/16) (eps/40)) :
    (q E).1 ≠ 0 ∧
      ‖(q E).2-homogeneousSpectralWKBLog 1 (p E) (v E)*(q E).1‖ ≤
        eps*‖p E‖*‖(q E).1‖ := by
  exact (spectralWKB_initial_relative_bounds eps heps R E hRE p v w q k hp hv hw hq hk hk0
    hkp hpD hvD hsmall hH hODE hN ha hsmallError).1

end DefocusingNLS

end OAI
