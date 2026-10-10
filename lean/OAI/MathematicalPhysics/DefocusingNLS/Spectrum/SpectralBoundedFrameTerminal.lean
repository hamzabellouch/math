import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPerturbedTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReverseTransfer

namespace OAI

/-! A bounded approximate oscillatory frame controls true solutions from their
terminal data. The bound uses the integrated residual, uniformly over every
subinterval. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_bounded_frame_terminal_bound
    (R E C c J : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (D U q : ℝ → ℂ × ℂ) (V e : ℝ → ℂ) (W : ℂ) (k : ℝ → ℝ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hVc : ContinuousOn V (Icc R E))
    (hec : ContinuousOn e (Icc R E)) (hkc : ContinuousOn k (Icc R E))
    (hk : ∀ t ∈ Icc R E, 0 < k t) (hW : c ≤ ‖W‖)
    (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t) = W)
    (hD : ∀ t ∈ Ioo R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Ioo R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField (V t) (q t)+(0,e t*(q t).1)) t)
    (hDb : ∀ t ∈ Icc R E, spectralShellNorm (k t) (D t) ≤ C)
    (hUb : ∀ t ∈ Icc R E, spectralShellNorm (k t) (U t) ≤ C)
    (hJ : (∫ t in R..E, ‖e t‖/(k t)^2) ≤ J) :
    ∀ r ∈ Icc R E, spectralShellNorm (k r) (q r) ≤
      (2*(2*C^2/c)*Real.exp ((2*C^2/c)*J))*spectralShellNorm (k E) (q E) := by
  let A := 2*C^2/c
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  intro r hr
  have hsub : Icc r E ⊆ Icc R E := Icc_subset_Icc hr.1 le_rfl
  have hRE : R ≤ E := hr.1.trans hr.2
  have hE : E ∈ Icc R E := ⟨hRE,le_rfl⟩
  have hg : ContinuousOn (fun t => ‖e t‖/(k t)^2) (Icc R E) :=
    hec.norm.div (hkc.pow 2) (fun t ht => pow_ne_zero _ (hk t ht).ne')
  have hi : (∫ t in r..E, ‖e t‖/(k t)^2) ≤ J := by
    apply le_trans _ hJ
    exact intervalIntegral.integral_mono_interval hr.1 hr.2 le_rfl
      (Filter.Eventually.of_forall (fun t => by positivity))
      (ContinuousOn.intervalIntegrable_of_Icc hRE hg)
  have hforward (u : ℝ → ℂ × ℂ) (huc : ContinuousOn u (Icc r E))
      (hu : ∀ t ∈ Ioo r E, HasDerivAt u (spectralScalarField (V t-e t) (u t)) t) :
      spectralShellNorm (k E) (u E) ≤
        (A*Real.exp (A*J))*spectralShellNorm (k r) (u r) := by
    have hu' (t : ℝ) (ht : t ∈ Ioo r E) : HasDerivAt u
        (spectralScalarField (V t) (u t)+(0,e t*(u t).1)) t := by
      apply (hu t ht).congr_deriv
      apply Prod.ext
      · simp only [spectralScalarField,Prod.fst_add,add_zero]
      · dsimp only [spectralScalarField,Prod.snd_add]
        ring
    have ht := spectral_perturbed_transfer r E C c hr.2 hC hc D U u V e W k
      (fun _ => 0) (hDc.mono hsub) (hUc.mono hsub) huc (hec.mono hsub)
      (hkc.mono hsub) continuousOn_const (fun t ht => hk t (hsub ht))
      (fun _ _ _ _ _ => le_rfl) hW (fun t ht => hdet t (hsub ht))
      (fun t ht => hD t ⟨hr.1.trans_lt ht.1,ht.2⟩)
      (fun t ht => hU t ⟨hr.1.trans_lt ht.1,ht.2⟩) hu'
      (fun t ht => by simpa only [Real.exp_zero,mul_one] using hDb t (hsub ht))
      (fun t ht => by simpa only [neg_zero,Real.exp_zero,mul_one] using hUb t (hsub ht))
      E ⟨hr.2,le_rfl⟩
    have hI : (∫ t in r..E, (2*C^2/c)*‖e t‖/(k t)^2) ≤ A*J := by
      simp only [mul_div_assoc,intervalIntegral.integral_const_mul]
      simpa only [A,mul_div_assoc] using mul_le_mul_of_nonneg_left hi hA
    calc
      _ ≤ A*spectralShellNorm (k r) (u r)*
          Real.exp (∫ t in r..E, (2*C^2/c)*‖e t‖/(k t)^2) := by
        simpa only [A,zero_sub,neg_zero,add_zero,zero_add] using ht
      _ ≤ A*spectralShellNorm (k r) (u r)*Real.exp (A*J) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hI)
          (mul_nonneg hA (spectralShellNorm_nonneg (k r) (hk r hr).le _))
      _ = _ := by ring
  have hq' (t : ℝ) (ht : t ∈ Ioo r E) :
      HasDerivAt q (spectralScalarField (V t-e t) (q t)) t := by
    apply (hq t ⟨hr.1.trans_lt ht.1,ht.2⟩).congr_deriv
    apply Prod.ext
    · simp only [spectralScalarField,Prod.fst_add,add_zero]
    · dsimp only [spectralScalarField,Prod.snd_add]
      ring
  have hrev := spectralScalar_reverse_transfer r E (k r) (k E) (A*Real.exp (A*J))
    hr.2 (hk r hr) (hk E hE) (fun t => V t-e t) ((hVc.sub hec).mono hsub)
    hforward q (hqc.mono hsub) hq'
  simpa only [A,mul_assoc] using hrev

end DefocusingNLS

end OAI
