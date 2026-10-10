import OAI.NumberTheory.CubicMoment.Estimates.LogCoefficientEnergy
import OAI.NumberTheory.CubicMoment.Estimates.StructuredHeightMass

namespace OAI

/-! The ordinary height mean with the actual logarithmic coefficient
cost retained, for the low-conductor part of the Poisson remainder. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem log_energy_dyadic_mean {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K D : ℝ) (a : ℕ), 0 ≤ K ∧ 1 ≤ D ∧
      ∀ (r : γ) (X : ι → ℝ), 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (h v e : Eisenstein) (ℓ : ℤ) (u T : ℝ), 0 < T →
      ((∫ t in T..2*T, ‖fullStructuredAngularSum R h v e ℓ (t+u) (W r) X‖^2)+
       (∫ t in -2*T..-T, ‖fullStructuredAngularSum R h v e ℓ (t+u) (W r) X‖^2))/T ≤
        K*(1+D*L r/T)*L r*(1+Real.log (L r))^a := by
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  let M : ℝ := ((2*Fintype.card ι)^(Fintype.card ι):ℕ)
  refine ⟨2*C*M*E,2*R^(Fintype.card ι),a,by dsimp [M]; positivity,?_,?_⟩
  · have hh := one_le_pow₀ hR (n := Fintype.card ι)
    linarith
  intro r X hL hX hprod h v e ℓ u T hT
  have hY : 1 ≤ R^(Fintype.card ι)*L r := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hL
  have hceil : (⌈R^(Fintype.card ι)*L r⌉₊:ℝ) ≤ 2*R^(Fintype.card ι)*L r := by
    linarith [Nat.ceil_lt_add_one (zero_le_one.trans hY)]
  have hb := fullStructured_dyadicMeanSquare hMV hC (zero_le_one.trans hR)
    (W r) X hX (hlo r) (hhi r) ⌈R^(Fintype.card ι)*L r⌉₊
    (by rw [hprod]; exact Nat.le_ceil _) h v e ℓ u hT
  have he := henergy r X hL hX hprod
  have hf : 1+(⌈R^(Fintype.card ι)*L r⌉₊:ℝ)/T ≤
      1+2*R^(Fintype.card ι)*L r/T :=
    add_le_add le_rfl (div_le_div_of_nonneg_right hceil hT.le)
  have hcoef : 0 ≤ 2*C*(1+(⌈R^(Fintype.card ι)*L r⌉₊:ℝ)/T)*M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
      (by positivity)) (Nat.cast_nonneg _)
  apply (hb.trans (mul_le_mul_of_nonneg_left he hcoef)).trans
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC))
      (Nat.cast_nonneg ((2*Fintype.card ι)^(Fintype.card ι))))
    (mul_nonneg (mul_nonneg hE (zero_le_one.trans hL))
      (pow_nonneg (show 0 ≤ 1+Real.log (L r) by linarith [Real.log_nonneg hL]) a))
  convert hm using 1
  dsimp [M]
  ring

end CubicFirstMoment

end

end OAI
