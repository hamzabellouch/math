import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeTransitionInput
import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductSharpMoments

namespace OAI

/-! Prime density supplies the logarithms in the uncorrected transition
variance; the diagonal is retained separately. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment

theorem single_prime_transition_log_variance {γ : Type*} (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C R M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hVM : ∀ x, ‖V x‖ ≤ M)
    (hcut : ∀ x, R < x → V x = 0)
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ), T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
      ‖smoothedDispersionVariance S β u V A‖ ≤ K*(
        A*L r/(1+Real.log (L r)) +
        A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2) := by
  obtain ⟨η,K,T,hη,hη1,hK,hvar⟩ := single_prime_transition_variance hSW hpub hHuxley
    hperiod hMV hC hGI hGQ V hV hV' hR hM hVM hcut L W hL hW hlo hhi 2 U
  obtain ⟨D,hD,hmoment⟩ := fullPrimeCoefficient_sharp_moments (ι := Unit) hpnt
    (R := 2) (by norm_num)
  let E := 2*D
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨η,K*(E+E^2+1),max T (max 2 (Real.exp 1)),hη,hη1,by positivity,?_⟩
  intro r A u hT hrough hAlo hAhi hu
  dsimp only
  let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
  let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have h2 : 2 ≤ L r := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hexp : Real.exp 1 ≤ L r := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hlog : 1 ≤ Real.log (L r) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hz : 0 < 1+Real.log (L r) := by linarith
  have hm := hmoment (fun _ : Unit => W r) (fun _ => L r) ((1+Real.log (L r))/2)
    (by positivity) (fun _ => h2) (fun _ => by linarith) (fun _ => hW1 r) 1
  have heq : D*(∏ _i : Unit, L r)/((1+Real.log (L r))/2)^(Fintype.card Unit) =
      E*L r/(1+Real.log (L r)) := by
    simp only [Fintype.prod_unique,Fintype.card_unique,pow_one]
    dsimp [E]
    field_simp
  rw [heq] at hm
  have hv := hvar r A u ((le_max_left _ _).trans hT) hrough hAlo hAhi hu
  change ‖smoothedDispersionVariance S β u V A‖ ≤ _ at hv ⊢
  have hm₁ : (∑ p ∈ S, ‖β p‖) ≤ E*L r/(1+Real.log (L r)) := hm.1
  have hm₂ : (∑ p ∈ S, ‖β p‖^2) ≤ E*L r/(1+Real.log (L r)) := hm.2
  have hm₁sq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _)) hm₁ 2
  have hpower : (L r)^(-(1/3:ℝ))*(L r)^2 = (L r)^(5/3:ℝ) := by
    rw [← Real.rpow_natCast (L r) 2,← Real.rpow_add hB]
    norm_num
  have hnorm : A*(E*L r/(1+Real.log (L r)))+
      A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(E*L r/(1+Real.log (L r)))^2+
      A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2 =
      E*(A*L r/(1+Real.log (L r)))+
      (E^2+1)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2) := by
    rw [div_pow,mul_pow,← hpower]
    ring
  apply hv.trans
  calc
    _ ≤ K*(A*(E*L r/(1+Real.log (L r)))+
        A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(E*L r/(1+Real.log (L r)))^2+
        A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2) := by
      gcongr
    _ = K*(E*(A*L r/(1+Real.log (L r)))+
        (E^2+1)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2)) := by rw [hnorm]
    _ ≤ K*(E+E^2+1)*(A*L r/(1+Real.log (L r))+
        A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2) := by
      have hx : 0 ≤ A*L r/(1+Real.log (L r)) := by positivity
      have hy : 0 ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2 := by positivity
      nlinarith [mul_nonneg (by positivity : 0 ≤ E^2+1) hx,mul_nonneg hE.le hy]

end CubicFirstMoment

end

end OAI
