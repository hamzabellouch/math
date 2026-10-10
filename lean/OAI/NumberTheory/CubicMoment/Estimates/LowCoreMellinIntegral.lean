import OAI.NumberTheory.CubicMoment.Estimates.LowCoreArithmeticTail
import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticMellinMoments
import OAI.NumberTheory.CubicMoment.Estimates.MellinMassIntegration
import OAI.NumberTheory.CubicMoment.Estimates.LowNoncubeMass

namespace OAI

/-! Full low-core Mellin integral: Kummer cancellation near zero, the
ordinary signed height mean in the tails. Both estimates are applied to
the actual finite structured sums. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma log_height_translate {z t u : ℝ} (hz : 2 ≤ z) (A U : ℕ)
    (ht : |t| ≤ z^A) (hu : |u| ≤ z^U) : |t+u| ≤ z^(max A U+1) := by
  have hz1 : 1 ≤ z := by linarith
  have ha := pow_le_pow_right₀ hz1 (le_max_left A U)
  have hu' := pow_le_pow_right₀ hz1 (le_max_right A U)
  calc
    _ ≤ |t|+|u| := abs_add_le _ _
    _ ≤ z^A+z^U := add_le_add ht hu
    _ ≤ 2*z^(max A U) := by linarith
    _ ≤ z*z^(max A U) := mul_le_mul_of_nonneg_right hz (pow_nonneg (by linarith) _)
    _ = _ := by rw [pow_succ]; ring

theorem low_core_mellin_integral_saving (hSW : KummerPrimeSiegelWalfisz)
    {C R c d₁ d₂ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hR : 1 ≤ R) (hc : 0 < c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (a k U q : ℕ) (ha : 0 < a) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      T₀ ≤ L r → (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      0 ≤ J → J ≤ (L r)^d₂ → H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (e : Eisenstein) (u ρ : ℝ), e ≠ 0 → norm e ≤ (L r)^d₁ →
      |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e 0 u (W r) X t) ≤
          K*J*(L r)^2/(1+Real.log (L r))^k := by
  obtain ⟨Kt,Tt,A,hKt,htail⟩ := low_core_arithmetic_mellin_tail hMV hC hR hW hlo hhi
    M hM V hV hV' a k q
  obtain ⟨Kn,Tn,hKn,hnear⟩ := low_noncube_mass hSW hW hlo hc hd₁ hd₂ hR a k (max A U+1) ha
  obtain ⟨D,hD,hmoment⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q 0
  refine ⟨Kn*D+Kt,max (max Tt Tn) (Real.exp 1),by positivity,?_⟩
  intro r X J H hT₀ hprod hrough hJ hJL hH e u ρ he heL hu hρ
  have hL : 1 ≤ L r := hW.length_one (r,Classical.arbitrary ι)
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hTt : Tt ≤ L r := (le_max_left Tt Tn).trans ((le_max_left _ _).trans hT₀)
  have hTn : Tn ≤ L r := (le_max_right Tt Tn).trans ((le_max_left _ _).trans hT₀)
  have hExp : Real.exp 1 ≤ L r := (le_max_right _ _).trans hT₀
  have hz : 2 ≤ 1+Real.log (L r) := by
    have hh := (Real.le_log_iff_exp_le hLp).mpr hExp
    linarith
  let T := (1+Real.log (L r))^A
  let F := arithmeticMellinCoefficient M hM V hV hV' ρ
  let G := fullStructuredHeightMass R H 1 e 0 u (W r) X
  let B := Kn*J*(L r)^2/(1+Real.log (L r))^k
  have hT1 : 1 ≤ T := one_le_pow₀ (by linarith)
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  have hX : ∀ i, 1 ≤ X i := fun i => (Real.one_le_rpow hL hc.le).trans (hrough i)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg := continuous_fullStructuredHeightMass R H 1 e 0 u (W r) X
  have hg0 := fullStructuredHeightMass_nonneg R H 1 e 0 u (W r) X
  obtain ⟨B₀,_hB₀,hB₀⟩ := fullStructuredHeightMass_bounded R H 1 e 0 u (W r) X
  have hfi : Integrable (fun t => (1+ρ)^q*‖F t‖) :=
    (arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm.const_mul _
  have hfg : Integrable (fun t => ((1+ρ)^q*‖F t‖)*G t) :=
    hfi.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hg0 t)]; exact hB₀ t))
  have hn : ∀ t : ℝ, |t| < T → G t ≤ B := by
    intro t ht
    have hs := log_height_translate hz A U ht.le hu
    simpa only [G,B,fullStructuredHeightMass,fullStructuredAngularSum_zero] using
      hnear r X J H hTn hprod hrough hJ hJL hH e he heL (t+u) hs
  have ht := htail r X J H hL hTt hX hprod hJ hH 1 e 0 u T ρ le_rfl hρ
  dsimp only at ht
  have htail' : (∫ t in Ici T, ((1+ρ)^q*‖F t‖)*G t)+
      (∫ t in Ici T, ((1+ρ)^q*‖F (-t)‖)*G (-t)) ≤
      Kt*J*(L r)^2/(1+Real.log (L r))^k := by
    simp only [mul_assoc,integral_const_mul]
    dsimp only [F,G]
    rw [← mul_add]
    apply ht.trans
    rw [div_mul_eq_div_div]
    have hbase : 0 ≤ Kt*J*(L r)^2/(1+Real.log (L r))^k := by positivity
    simpa only [mul_assoc] using div_le_self hbase hT1
  have hi := integral_local_and_signed_tail hfi (fun t => by positivity) hfg hTp hB hn htail'
  have hm : (∫ t : ℝ, (1+ρ)^q*‖F t‖) ≤ D := by
    rw [integral_const_mul]
    simpa only [pow_zero,one_mul] using hmoment ρ hρ
  have hi' := hi.trans (add_le_add (mul_le_mul_of_nonneg_left hm hB) le_rfl)
  simp only [mul_assoc,integral_const_mul] at hi'
  convert hi' using 1
  dsimp only [B,F,G]
  ring

end CubicFirstMoment

end

end OAI
