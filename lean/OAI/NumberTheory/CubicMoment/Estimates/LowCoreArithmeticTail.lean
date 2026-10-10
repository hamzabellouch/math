import OAI.NumberTheory.CubicMoment.Estimates.SignedMellinTail
import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticMellinKernel
import OAI.NumberTheory.CubicMoment.Estimates.LowCoreHeightSaving
import OAI.NumberTheory.CubicMoment.Estimates.StructuredHeightContinuity

namespace OAI

/-! The low-core tail in the arithmetic height appearing in the separated
Poisson kernel, including the precise 2π change of variables.
Only the published ordinary Montgomery--Vaughan input is used here. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem low_core_arithmetic_mellin_tail {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (a k q : ℕ) :
    ∃ (K T₀ : ℝ) (A : ℕ), 0 ≤ K ∧
      ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → T₀ ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 0 ≤ J →
      H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (v e : Eisenstein) (ℓ : ℤ) (u T ρ : ℝ), (1+Real.log (L r))^A ≤ T → 0 ≤ ρ →
      let F := arithmeticMellinCoefficient M hM V hV hV' ρ
      let G := fullStructuredHeightMass R H v e ℓ u (W r) X
      (1+ρ)^q*((∫ t in Ici T, ‖F t‖*G t)+(∫ t in Ici T, ‖F (-t)‖*G (-t))) ≤
        K*J*(L r)^2/((1+Real.log (L r))^k*T) := by
  obtain ⟨K,T₀,A,hK,hmean⟩ := low_core_height_log_saving hMV hC hR hW hlo hhi a k
  obtain ⟨D,hD,hdecay⟩ := arithmeticMellinCoefficient_quadratic_decay M hM V hV hV' q
  refine ⟨4*K*D,T₀,A,by positivity,?_⟩
  intro r X J H hL hTL hX hprod hJ hH v e ℓ u T ρ hT hρ
  dsimp only
  let G := fullStructuredHeightMass R H v e ℓ u (W r) X
  let F := arithmeticMellinCoefficient M hM V hV hV' ρ
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hTp : 0 < T := (pow_pos hz A).trans_le hT
  have hg := continuous_fullStructuredHeightMass R H v e ℓ u (W r) X
  have hg0 := fullStructuredHeightMass_nonneg R H v e ℓ u (W r) X
  obtain ⟨B,_hB,hB⟩ := fullStructuredHeightMass_bounded R H v e ℓ u (W r) X
  have hF : Continuous F := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hfg : Integrable (fun t => ((1+ρ)^q*‖F t‖)*G t) :=
    ((arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm.const_mul _).mul_bdd
      hg.aestronglyMeasurable (Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hg0 t)]
        exact hB t))
  have hb : 0 ≤ K*J*(L r)^2/(1+Real.log (L r))^k := by positivity
  have ht := weighted_signed_mellin_tail (continuous_const.mul hF.norm) hg hg0 hfg
    hTp hb hD.le (fun S hS => hmean r X J H hL hTL hX hprod hJ hH v e ℓ u S (hT.trans hS))
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
