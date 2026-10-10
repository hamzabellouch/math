import OAI.NumberTheory.CubicMoment.Estimates.LowCoreHeightMean
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeCutoffPowers

namespace OAI

/-! Above a fixed logarithmic height, the actual ordinary mean supplies
every logarithmic saving on the small-core frequency set. -/
noncomputable section
open Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma logarithmic_height_factor {L z D T : ℝ} (hL : 0 ≤ L) (hz : 1 ≤ z)
    (hD : 0 ≤ D) (b k : ℕ) (hlog : z^(b+k) ≤ L) (hT : z^(b+k) ≤ T) :
    (1+D*L/T)*L*z^b ≤ (1+D)*L^2/z^k := by
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hT0 : 0 < T := (pow_pos hz0 _).trans_le hT
  apply (le_div_iff₀ (pow_pos hz0 k)).mpr
  calc
    _ = L*z^(b+k)+D*L^2*(z^(b+k)/T) := by rw [pow_add]; ring
    _ ≤ L*L+D*L^2*1 := add_le_add
      (mul_le_mul_of_nonneg_left hlog hL)
      (mul_le_mul_of_nonneg_left ((div_le_one hT0).mpr hT) (mul_nonneg hD (sq_nonneg _)))
    _ = _ := by ring

theorem low_core_height_log_saving {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (a k : ℕ) :
    ∃ (K T₀ : ℝ) (A : ℕ), 0 ≤ K ∧
      ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → T₀ ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 0 ≤ J →
      H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (v e : Eisenstein) (ℓ : ℤ) (u T : ℝ), (1+Real.log (L r))^A ≤ T →
      ((∫ t in T..2*T, fullStructuredHeightMass R H v e ℓ u (W r) X t)+
       (∫ t in -2*T..-T, fullStructuredHeightMass R H v e ℓ u (W r) X t))/T ≤
        K*J*(L r)^2/(1+Real.log (L r))^k := by
  obtain ⟨K,D,b,hK,hD,hmean⟩ := low_core_height_mean hMV hC hR hW hlo hhi a
  have hev := exclusion_log_absorption (c := 1) (d := 0) (ε := 1)
    (by norm_num) (by norm_num) (C := 1) (by norm_num) (b+k) 0
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hev
  refine ⟨K*(1+D),T₀,b+k,mul_nonneg hK (by linarith),?_⟩
  intro r X J H hL hTL hX hprod hJ hH v e ℓ u T hT
  have hz : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hlog := hT₀ (L r) hTL (L r) 1 (by norm_num) (by simp) (by simp)
  simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hlog
  have hTpos : 0 < T := (pow_pos (zero_lt_one.trans_le hz) _).trans_le hT
  apply (hmean r X J H hL hX hprod hJ hH v e ℓ u T hTpos).trans
  have hm := mul_le_mul_of_nonneg_left
    (logarithmic_height_factor (zero_le_one.trans hL) hz (zero_le_one.trans hD) b k hlog hT)
    (mul_nonneg hK hJ)
  convert hm using 1 <;> ring

end CubicFirstMoment

end

end OAI
