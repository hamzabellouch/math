import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDeriv_exp_real (j : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ j Complex.exp z‖ = ‖Complex.exp z‖ := by
  have h : ContDiffAt ℂ (j : ℕ∞ω) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

lemma norm_unitMode (τ : ℝ) (p : Base) : ‖unitMode τ p‖ = 1 := by
  have he : Complex.I / (τ : ℂ) * (p.1 : ℂ) = ((p.1 / τ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  unfold unitMode
  rw [he]
  exact Complex.norm_exp_ofReal_mul_I (p.1 / τ)

lemma contDiff_unitMode (τ : ℝ) : ContDiff ℝ ∞ (unitMode τ) := by
  have hL : ContDiff ℝ ∞ (fun p : Base => (Complex.I / (τ : ℂ)) * (p.1 : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).contDiff
  exact hL.cexp



lemma weighted_unitMode {U : Set Base} (hU : IsOpen U) {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    WeightedBound U τ m 1 (unitMode τ) := by
  let L : Base →L[ℝ] ℂ := (Complex.I / (τ : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ))
  have hL : ‖L‖ ≤ τ⁻¹ := by
    apply L.opNorm_le_bound (inv_nonneg.mpr hτ.le)
    intro p
    change ‖Complex.I / (τ : ℂ) * (p.1 : ℂ)‖ ≤ _
    simp only [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le,
      one_div]
    exact mul_le_mul_of_nonneg_left (norm_fst_le p) (inv_nonneg.mpr hτ.le)
  intro j hj p hp
  rw [iteratedFDerivWithin_of_isOpen j hU hp]
  have he : unitMode τ = Complex.exp ∘ L := rfl
  rw [he, L.iteratedFDeriv_comp_right (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)) p
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
  have hh := (iteratedFDeriv ℝ j Complex.exp (L p)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)
  have hnorm : ‖iteratedFDeriv ℝ j Complex.exp (L p)‖ = 1 := by
    rw [norm_iteratedFDeriv_exp_real]
    exact norm_unitMode τ p
  rw [hnorm] at hh
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul] at hh
  calc
    _ ≤ τ ^ j * ‖L‖ ^ j := mul_le_mul_of_nonneg_left hh (pow_nonneg hτ.le _)
    _ ≤ τ ^ j * (τ⁻¹) ^ j := by gcongr
    _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hτ.ne', one_pow]

lemma contDiffOn_oscillate {n : ℕ} {U : Set Base} {Z : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) : ContDiffOn ℝ ∞ (oscillate τ Z) U :=
  (contDiff_unitMode τ).contDiffOn.smul hZ



lemma weighted_oscillate {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {τ s C : ℝ} {m : ℕ} {Z : Field n} (hτ : 0 < τ) (hτs : τ ≤ s)
    (hC : 0 ≤ C) (hZ : ContDiffOn ℝ ∞ Z U) (hb : WeightedBound U s m C Z) :
    WeightedBound U τ m (2 ^ m * C) (oscillate τ Z) := by
  have hs : 0 ≤ s := hτ.le.trans hτs
  have hz := hb.shrink_scale hτ.le hτs
  apply WeightedBound.pi hU.uniqueDiffOn hτ (by positivity)
  · intro i
    exact contDiffOn_pi.mp (contDiffOn_oscillate hZ τ) i
  · intro i
    have hh := (weighted_unitMode hU hτ m).mul hU.uniqueDiffOn hτ.le (by norm_num) hC
      (contDiff_unitMode τ).contDiffOn (contDiffOn_pi.mp hZ i)
      (hz.component hU.uniqueDiffOn hτ.le hC hZ i)
    simpa only [mul_one, oscillate, Pi.smul_apply, smul_eq_mul] using hh

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

def forcedModeConstant (n m : ℕ) (K : ℝ) : ℕ → ℝ
  | 0 => initialConstant n m K
  | q + 1 => forcedModeConstant n m K q +
      initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1)

lemma forcedModeConstant_nonneg (n m q : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ forcedModeConstant n m K q := by
  induction q with
  | zero => exact initialConstant_nonneg _ _ hK
  | succ q ih => exact add_nonneg ih (mul_nonneg (initialConstant_nonneg _ _ hK)
      (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _))




theorem weighted_modeApprox {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m (forcedModeConstant n m K q * C)
      (modeApprox τ G V f q) := by
  induction q with
  | zero =>
    simpa only [Nat.add_zero, forcedModeConstant, modeApprox] using
      weighted_initialAmplitude hτ h hs hτs hs1 hK hC hc hf hVsm hb hbV
  | succ q ih =>
    have hi := ih (hc.mono_order (by omega)) (hb.mono_order (by omega))
      (hbV.mono_order (by omega))
    have hm : m + 1 + q + 1 = m + (q + 1) + 1 := by omega
    have hce : ReconstructionCoefficientBound G U s (m + 1 + q + 1) K := hm ▸ hc
    have hbe : WeightedBound U s (m + 1 + q + 1) C f := hm ▸ hb
    have hbVe : WeightedBound U s (m + 1 + q + 1) C V := hm ▸ hbV
    have hr := weighted_residual_modeApprox hτ hG h hs hs1 hK hC hf hVsm
      hX hY hV q (m + 1) hce.toFullModeCoefficientBound hbe hbVe
    have hrsm := contDiffOn_residual τ h (contDiffOn_modeApprox τ h hVsm hf q) hf
    have hn : 0 ≤ fullErrorConstant n (m + 1 + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C :=
      mul_nonneg (mul_nonneg (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _)
        (pow_nonneg (div_nonneg hτ.le hs.le) _)) hC
    have hp := weighted_initialAmplitude hτ h hs hτs hs1 hK hn
      (hc.mono_order (by omega)) hrsm (V := fun _ => 0) contDiffOn_const hr
      ((weightedBound_zero U s (m + 1)).mono_const hn)
    have hp' : WeightedBound U s m
        (initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * C)
        (zeroParametrix τ G (residual τ G f (modeApprox τ G V f q))) := by
      apply hp.mono_const
      have hpow : (τ / s) ^ (q + 1) ≤ 1 := pow_le_one₀ (div_nonneg hτ.le hs.le)
        ((div_le_one hs).2 hτs)
      calc
        _ = (initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * C) *
          (τ / s) ^ (q + 1) := by ring
        _ ≤ _ := mul_le_of_le_one_right
          (mul_nonneg (mul_nonneg (initialConstant_nonneg _ _ hK)
            (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _)) hC) hpow
    have hpSm := contDiffOn_initialAmplitude τ h (V := fun _ => 0) contDiffOn_const hrsm
    have hh := hi.sub h.isOpen.uniqueDiffOn hs.le
      (contDiffOn_modeApprox τ h hVsm hf q) hpSm hp'
    have he : forcedModeConstant n m K q * C +
        initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * C =
        forcedModeConstant n m K (q + 1) * C := by
      simp only [forcedModeConstant]; ring
    rw [he] at hh
    exact hh

end ClosedSurfaceR4.SmallModes

end

end OAI
