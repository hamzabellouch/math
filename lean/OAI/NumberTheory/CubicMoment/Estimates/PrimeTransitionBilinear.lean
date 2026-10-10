import OAI.NumberTheory.CubicMoment.Estimates.PrimeTransitionDensity
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTransitionScale

namespace OAI

/-! The uncorrected one-prime/two-prime transition estimate. The outer
energy assumption can be filled by the actual two-coordinate PNT count. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem single_prime_transition_bilinear {γ : Type*} (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C Q M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hQ : 1 ≤ Q) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ) (P : Finset Eisenstein) (α : Eisenstein → ℂ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      (∀ a ∈ P, primary a ∧ norm a/A ∈ Set.Icc 1 Q) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A/(1+Real.log (L r))^2 →
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
      ‖∑ a ∈ P, ∑ p ∈ S, α a*β p*gauss (a*p)*normTwist u (a*p)‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
  let V := fun x => (dispersionCutoff Q x:ℂ)
  have hVM (x : ℝ) : ‖V x‖ ≤ 1 := by
    dsimp [V]
    rw [Complex.norm_real,Real.norm_of_nonneg (dispersionCutoff_nonneg Q x)]
    exact (mul_le_mul (Real.smoothTransition.le_one _)
      (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul 1)
  obtain ⟨η,K,T,hη,hη1,hK,hvar⟩ := single_prime_transition_log_variance hpnt hSW hpub
    hHuxley hperiod hMV hC hGI hGQ V (dispersionCutoff_complex_compact Q)
    (dispersionCutoff_complex_smooth Q) (by linarith : 0 ≤ Q+1) (by norm_num)
    hVM (fun x hx => by simp only [V,dispersionCutoff_high hx,Complex.ofReal_zero])
    L W hL hW hlo hhi hW1 U
  refine ⟨η,Real.sqrt (2*M*K)+1,T,hη,hη1,by positivity,?_⟩
  intro r A u P α hT hrough hAlo hAhi hu hP henergy
  dsimp only
  let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
  let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hZ : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hS (p : Eisenstein) (hp : p ∈ S) : primary p :=
    (fullSquarefreePrimeSupport_primary 2 (fun _ : Unit => W r) (fun _ => L r) 1 hp).1
  have hc := bilinear_full_variance_bound_sq P S α β u (fun a ha => (hP a ha).1) hS
    (dispersionCutoff Q) (dispersionCutoff_nonneg Q) (dispersionCutoff_complex_compact Q)
    (dispersionCutoff_complex_smooth Q) hA (fun a ha => by rw [dispersionCutoff_one (hP a ha).2])
  have hv := hvar r A u hT hrough hAlo hAhi hu
  change ‖smoothedDispersionVariance S β u V A‖ ≤ _ at hv
  have hb := hc.trans (mul_le_mul henergy hv (_root_.norm_nonneg _) (by positivity))
  have hs := prime_transition_cauchy_scale hA hB hZ hK.le hM hAhi hb
  apply hs.trans
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  gcongr
  linarith

end CubicFirstMoment

end

end OAI
