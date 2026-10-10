import OAI.NumberTheory.CubicMoment.Estimates.LogEnergyMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.LowCoreSupport

namespace OAI

/-! The actual finite small-core frequency set at arbitrary height.
This mean-value bound complements the low-height Kummer prime estimate. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem low_core_height_mean {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (a : ℕ) :
    ∃ (K D : ℝ) (b : ℕ), 0 ≤ K ∧ 1 ≤ D ∧
      ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 0 ≤ J →
      H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (v e : Eisenstein) (ℓ : ℤ) (u T : ℝ), 0 < T →
      ((∫ t in T..2*T, fullStructuredHeightMass R H v e ℓ u (W r) X t)+
       (∫ t in -2*T..-T, fullStructuredHeightMass R H v e ℓ u (W r) X t))/T ≤
        K*J*(1+D*L r/T)*L r*(1+Real.log (L r))^b := by
  obtain ⟨K,D,b,hK,hD,hbound⟩ := log_energy_dyadic_mean hMV hC hR hW hlo hhi
  refine ⟨324*K,D,a+b,by positivity,hD,?_⟩
  intro r X J H hL hX hprod hJ hH v e ℓ u T hT
  have hz : 0 ≤ Real.log (L r) := Real.log_nonneg hL
  have hcard : (H.card:ℝ) ≤ 324*(1+Real.log (L r))^a*J := by
    calc
      _ ≤ ((lowNoncubeSupport ((Real.log (L r))^a) J).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hH)
      _ ≤ 324*(Real.log (L r))^a*J := lowNoncubeSupport_card (pow_nonneg hz _) hJ
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hz (by linarith) _) (by norm_num)) hJ
  have hm := fullStructuredHeightMass_le H v e ℓ u (W r) X
    (fun h _ => hbound r X hL hX hprod h v e ℓ u T hT)
  apply hm.trans
  have hfactor : 0 ≤ K*(1+D*L r/T)*L r*(1+Real.log (L r))^b := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg hK (by positivity)
      · exact zero_le_one.trans hL
    · exact pow_nonneg (by linarith) _
  apply (mul_le_mul_of_nonneg_right hcard hfactor).trans_eq
  rw [pow_add]
  ring

end CubicFirstMoment

end

end OAI
