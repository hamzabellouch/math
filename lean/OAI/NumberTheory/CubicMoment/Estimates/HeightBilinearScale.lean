import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinear
import OAI.NumberTheory.CubicMoment.Estimates.CorrectedBilinearScale
import OAI.NumberTheory.CubicMoment.Estimates.DispersionCutoff

namespace OAI

/-! Normalization of the genuine height-averaged bilinear estimate. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma dyadicHeightMean_nonneg {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ}
    (hT : 0 < T) (h : ∀ t, 0 ≤ f t) : 0 ≤ dyadicHeightMean f T := by
  have hm := dyadicHeightMean_mono continuous_const hf hT (fun t _ => h t)
  simpa only [dyadicHeightMean_const 0 hT.ne',mul_zero] using hm

lemma dyadicHeightMean_norm_le_of_sq_le {f : ℝ → ℂ} (hf : Continuous f)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ R^2) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤ 2*R := by
  have hm := dyadicHeightMean_mono
    (f := fun t => (2*R)*‖f t‖) (g := fun t => ‖f t‖^2+R^2)
    (continuous_const.mul hf.norm) ((hf.norm.pow 2).add continuous_const) hT
    (fun t _ => by nlinarith [sq_nonneg (‖f t‖-R)])
  rw [dyadicHeightMean_const_mul,
    dyadicHeightMean_add (f := fun t => ‖f t‖^2) (g := fun _ => R^2)
      (hf.norm.pow 2) continuous_const,
    dyadicHeightMean_const _ hT.ne'] at hm
  nlinarith [sq_pos_of_pos hR]

lemma height_bilinear_error_log_saving {f : ℝ → ℂ} (hf : Continuous f)
    {T M K A L z E V : ℝ} (hT : 0 < T)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 < A) (hL : 0 < L) (hz : 0 < z)
    (k d : ℕ) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (herror : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ E*V)
    (henergy : E ≤ M*A*z^d)
    (hmass : V ≤ K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤
      (2*(Real.sqrt (M*K)+1))*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  let B := dyadicHeightMean (fun t => ‖f t‖^2) T
  have hB : 0 ≤ B := dyadicHeightMean_nonneg (hf.norm.pow 2) hT (fun _ => sq_nonneg _)
  have hroot : ‖(Real.sqrt B:ℂ)‖^2 ≤ E*V := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hB]
    exact herror
  have hb := bilinear_error_log_saving hM hK hA hL hz k d hE hV hroot henergy hmass
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hb
  let R := (Real.sqrt (M*K)+1)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k
  have hR : 0 < R := by dsimp [R]; positivity
  have hbr : Real.sqrt B ≤ R := hb.trans (by
    dsimp [R]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : Real.sqrt (M*K) ≤ Real.sqrt (M*K)+1)
          (Real.rpow_nonneg hA.le _)) (Real.rpow_nonneg hL.le _)) (pow_nonneg hz.le _))
  have hsq : B ≤ R^2 := by nlinarith [Real.sq_sqrt hB,Real.sqrt_nonneg B]
  have hm := dyadicHeightMean_norm_le_of_sq_le hf hT hR hsq
  convert hm using 1
  dsimp [R]
  ring

variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rough_prime_height_bilinear
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R Q M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (k d : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u T : ℝ)
        (P : Finset Eisenstein) (α : Eisenstein → ℂ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      (∀ a ∈ P, primary a ∧ norm a/A ∈ Set.Icc 1 Q) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A*(1+Real.log (L r))^d →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
          α a*fullPrimeCoefficient R (W r) X b*gauss (a*b)*normTwist (u+t) (a*b)‖) T ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hvar⟩ := height_full_variance_saving
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    (fun x => (dispersionCutoff Q x:ℂ)) (dispersionCutoff_complex_compact Q)
    (dispersionCutoff_complex_smooth Q) (2*k+d)
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G,K₀,L₀,m,hK₀,hvar⟩ := hvar L W hL hW hlo hhi
  refine ⟨G,2*(Real.sqrt (M*K₀)+1),L₀,m,by positivity,?_⟩
  intro r X A e u T P α hL₀ hprod hX hAlo hAhi he heN hT hThi hu hP henergy
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hAp : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := fullPrimeCoefficient R (W r) X
  have hS : ∀ b ∈ S, primary b := fun b hb => (fullSquarefreePrimeSupport_primary R (W r) X e hb).1
  have hcont : Continuous (fun t => ∑ a ∈ P, ∑ b ∈ S,
      α a*β b*gauss (a*b)*normTwist (u+t) (a*b)) := by
    apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    exact continuous_const.mul ((continuous_normTwist (a*b)).comp (continuous_const.add continuous_id))
  exact height_bilinear_error_log_saving hcont hTp hM hK₀.le hAp hLp hz k d
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (dyadicHeightMean_nonneg
      (((continuous_smoothedDispersionVariance S hS β (fun x => (dispersionCutoff Q x:ℂ))
        (dispersionCutoff_complex_compact Q) (dispersionCutoff_complex_smooth Q) hAp).comp
          (continuous_const.add continuous_id)).norm) hTp (fun _ => _root_.norm_nonneg _))
    (height_bilinear_full_variance_bound_sq P S α β u (fun a ha => (hP a ha).1) hS
      (dispersionCutoff Q) (dispersionCutoff_nonneg Q) (dispersionCutoff_complex_compact Q)
      (dispersionCutoff_complex_smooth Q) hAp hTp
      (fun a ha => (dispersionCutoff_one (hP a ha).2).ge))
    henergy (hvar r X A e u T hL₀ hprod hX hAlo hAhi he heN hT hThi hu)

end CubicFirstMoment

end

end OAI
