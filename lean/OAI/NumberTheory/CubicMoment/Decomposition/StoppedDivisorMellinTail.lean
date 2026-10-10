import OAI.NumberTheory.CubicMoment.Estimates.DivisorLowAllFrequency
import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticMellinKernel
import OAI.NumberTheory.CubicMoment.Estimates.SignedMellinTail

namespace OAI

/-! The entire arithmetic Mellin tail of bounded squarefree coefficients.
The mean bound is the proved divisor-weighted low-height theorem, uniformly
in the height shift. It needs no prime-cancellation hypothesis. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_divisor_arithmetic_mellin_tail
    (hpnt : PrimaryPrimePNT) {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hHuxley : HuxleyAdditiveLargeSieve)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
        (Z : ℕ) (B A u T ρ : ℝ),
      65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ ρ →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ A) → 8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      let F := arithmeticMellinCoefficient M hM V hV hV' ρ
      let G := fun t => divisorCharacterMass S H U β (t+u)
      (1+ρ)^q*((∫ t in Ici T, ‖F t‖*G t)+(∫ t in Ici T, ‖F (-t)‖*G (-t))) ≤
        K*A^2*(Z:ℝ)^2*B^(1/3:ℝ)/((1+Real.log Z)^k*T) := by
  obtain ⟨K,Ct,hK,hmean⟩ := divisor_all_frequency_low_log_saving hpnt hMV hC hHuxley k
  obtain ⟨D,hD,hdecay⟩ := arithmeticMellinCoefficient_quadratic_decay M hM V hV hV' q
  refine ⟨4*K*D,Ct,by positivity,?_⟩
  intro S H U β Z B A u T ρ hZ hB hA hT hρ hU hS hβ hsize hH
  dsimp only
  let F := arithmeticMellinCoefficient M hM V hV hV' ρ
  let G := fun t => divisorCharacterMass S H U β (t+u)
  let E := ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d,p) ∣ a)).card*
    ∑ a ∈ S.filter (fun a => (∏ p ∈ d,p) ∣ a), ‖β a‖^2
  have hG : Continuous G :=
    (divisorCharacterMass_continuous S H U β).comp (continuous_id.add continuous_const)
  have hG0 (t : ℝ) : 0 ≤ G t :=
    Finset.sum_nonneg (fun _ _ => finiteCharacterMass_nonneg _ _ _ _)
  have hGb (t : ℝ) : ‖G t‖ ≤ E :=
    divisorCharacterMass_bound S H U β (fun a ha => (hS a ha).1) (t+u)
  have hF : Continuous F := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hfg : Integrable (fun t => ((1+ρ)^q*‖F t‖)*G t) :=
    ((arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm.const_mul _).mul_bdd
      hG.aestronglyMeasurable (Eventually.of_forall hGb)
  have hZ1 : 1 ≤ (Z:ℝ) := by linarith
  have hL : 0 < 1+Real.log (Z:ℝ) := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hL Ct).trans_le hT
  have hb : 0 ≤ K*A^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by positivity
  have ht := weighted_signed_mellin_tail (continuous_const.mul hF.norm) hG hG0 hfg
    hTp hb hD.le
    (fun T' hT' => hmean S H U β Z B T' A u hZ hB hA (hT.trans hT') hU hS hβ hsize hH)
    (fun t ht => by
      have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
      apply (le_div_iff₀ (sq_pos_of_ne_zero ht0)).mpr
      simpa only [Pi.mul_apply,F,Real.norm_eq_abs,sq_abs,mul_assoc,mul_left_comm,mul_comm]
        using hdecay ρ hρ t)
  simp only [Pi.mul_apply,mul_assoc,integral_const_mul] at ht
  dsimp only [F] at ht
  convert ht using 1 <;> ring

end CubicFirstMoment

end

end OAI
