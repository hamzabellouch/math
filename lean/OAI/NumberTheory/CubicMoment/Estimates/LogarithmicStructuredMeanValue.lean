import OAI.NumberTheory.CubicMoment.Estimates.FullStructuredMeanValue

namespace OAI

/-! Uniform height means for actual logarithmically varying prime weights. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeCoefficient_log_energy {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ), 1 ≤ L r → T₀ ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R (W r) X),
        ‖fullPrimeCoefficient R (W r) X z‖^2) ≤ (L r)^(1+ε) := by
  obtain ⟨T₀,h⟩ := logarithmic_structured_coefficient_energy hW hR hε hlo hhi
  refine ⟨T₀,?_⟩
  intro r X hL hT₀ hX hprod
  unfold fullPrimeCoefficient
  rw [fullPrimeSupport_eq_product_cutoff hR (W r) X hX (hhi r)]
  exact h r X _ hL hT₀ (fun i => zero_lt_one.trans_le (hX i)) hprod

theorem logarithmic_fullStructured_dyadicMeanSquare {C R ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hR : 1 ≤ R) (hε : 0 < ε)
    (L : γ → ℝ) (W : γ → ι → ℝ → ℂ)
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ), 1 ≤ L r → T₀ ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (h v e : Eisenstein) (ℓ : ℤ) (u T : ℝ), 0 < T →
      ((∫ t in T..2*T, ‖fullStructuredAngularSum R h v e ℓ (t+u) (W r) X‖^2) +
       (∫ t in -2*T..-T, ‖fullStructuredAngularSum R h v e ℓ (t+u) (W r) X‖^2))/T ≤
        (2*C*((2*Fintype.card ι)^(Fintype.card ι):ℕ)) *
          (1+2*R^(Fintype.card ι)*L r/T)*(L r)^(1+ε) := by
  obtain ⟨T₀,henergy⟩ := fullPrimeCoefficient_log_energy hW
    (zero_le_one.trans hR) hε hlo hhi
  refine ⟨T₀,?_⟩
  intro r X hL hT₀ hX hprod h v e ℓ u T hT
  have hK : 1 ≤ R^(Fintype.card ι) := one_le_pow₀ hR
  have hY : 1 ≤ R^(Fintype.card ι)*L r := one_le_mul_of_one_le_of_one_le hK hL
  have hceil : (⌈R^(Fintype.card ι)*L r⌉₊:ℝ) ≤ 2*R^(Fintype.card ι)*L r := by
    linarith [Nat.ceil_lt_add_one (show 0 ≤ R^(Fintype.card ι)*L r from zero_le_one.trans hY)]
  have hb := fullStructured_dyadicMeanSquare hMV hC (zero_le_one.trans hR)
    (W r) X hX (hlo r) (hhi r) ⌈R^(Fintype.card ι)*L r⌉₊
    (by rw [hprod]; exact Nat.le_ceil _) h v e ℓ u hT
  have hE := henergy r X hL hT₀ hX hprod
  have hf : 1+(⌈R^(Fintype.card ι)*L r⌉₊:ℝ)/T ≤
      1+2*R^(Fintype.card ι)*L r/T :=
    add_le_add (le_refl 1) (div_le_div_of_nonneg_right hceil hT.le)
  calc
    _ ≤ 2*C*(1+(⌈R^(Fintype.card ι)*L r⌉₊:ℝ)/T)*
        ((2*Fintype.card ι)^(Fintype.card ι):ℕ)*(L r)^(1+ε) :=
      hb.trans (mul_le_mul_of_nonneg_left hE (by positivity))
    _ ≤ 2*C*(1+2*R^(Fintype.card ι)*L r/T)*
        ((2*Fintype.card ι)^(Fintype.card ι):ℕ)*(L r)^(1+ε) := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
