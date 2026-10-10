import OAI.NumberTheory.CubicMoment.Estimates.TypeIPowers

namespace OAI

/-! The Type-I height bound with the paper's exponents, obtained by
absorbing the fixed logarithmic coefficient loss. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

lemma typeI_log_power_bound (B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℝ, 0 < L ∧ ∀ X : ℝ, 1 ≤ X → (Real.log X)^B ≤ L*X^δ := by
  cases B with
  | zero =>
    refine ⟨1,zero_lt_one,?_⟩
    intro X hX
    simpa using Real.one_le_rpow hX hδ.le
  | succ n =>
    let η : ℝ := δ/(n+1)
    have hn : (0:ℝ) < n+1 := by positivity
    have hη : 0 < η := div_pos hδ hn
    refine ⟨(1/η)^(n+1),pow_pos (one_div_pos.mpr hη) _,?_⟩
    intro X hX
    have hXp : 0 < X := zero_lt_one.trans_le hX
    have hl := Real.log_le_rpow_div hXp.le hη
    have hp := pow_le_pow_left₀ (Real.log_nonneg hX) hl (n+1)
    have he : (X^η)^(n+1) = X^δ := by
      rw [← Real.rpow_mul_natCast hXp.le]
      congr 1
      dsimp [η]
      push_cast
      exact div_mul_cancel₀ δ hn.ne'
    calc
      _ ≤ (X^η/η)^(n+1) := hp
      _ = (1/η)^(n+1)*X^δ := by rw [div_eq_mul_inv,mul_pow,he]; ring

lemma typeI_principal_log_bound {X R δ : ℝ} (hX : 1 ≤ X) (hR : 0 < R)
    (hRX : R ≤ X) (hδ : 0 ≤ δ) {L : ℝ} (B : ℕ)
    (hlog : (Real.log X)^B ≤ L*X^δ) :
    X^(1/2+δ)*R^(3/4+δ)*(Real.log X)^B ≤
      L*X^(1/2+3*δ)*R^(3/4:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  calc
    _ ≤ (X^(1/2+2*δ)*R^(3/4:ℝ))*(L*X^δ) := mul_le_mul
      (typeI_principal_power_bound hXp hR hRX hδ) hlog
      (pow_nonneg (Real.log_nonneg hX) _) (by positivity)
    _ = L*(X^(1/2+2*δ)*X^δ)*R^(3/4:ℝ) := by ring
    _ = _ := by rw [← Real.rpow_add hXp,show (1/2+2*δ)+δ = 1/2+3*δ by ring]

/-- The literal zero-angular Type-I height estimate. The coefficient
hypothesis is its explicit divisor-bounded L1 consequence; all analytic
inputs are the cited published continuation and HB estimates. -/
theorem typeI_height_of_published {W : Eisenstein → ℝ → ℂ} (hW : UniformLogWeights W)
    {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (D B : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (S : Finset Eisenstein) (a : Eisenstein → ℂ)
      (R U T : ℝ), 1 ≤ R → 1 ≤ U → 1 ≤ T →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖a r‖) ≤ K*R*(Real.log (R*U))^B →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W r) U t‖)+
       (∫ t in -(2*T)..(-T), ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W r) U t‖))/T ≤
        C*(R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T+
        E*(R*U)^(5/6:ℝ)*(Real.log (R*U))^B/T^D := by
  let δ := min (ε/3) (1/24)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδs : δ < 1/12 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : 3*δ ≤ ε := by have := min_le_left (ε/3) (1/24:ℝ); dsimp [δ]; linarith
  obtain ⟨C,E,hC,hE,hbound⟩ := typeI_finite_levels hW hF hGrowth hHB hδ hδs D
  obtain ⟨L,hL,hlog⟩ := typeI_log_power_bound B hδ
  refine ⟨C*2^(1/4+2*δ)*K*L,E*K,by positivity,by positivity,?_⟩
  intro S a R U T hR hU hT hS ha
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 1 ≤ R*U := by nlinarith
  have hRX : R ≤ R*U := le_mul_of_one_le_right hRp.le hU
  have hA : (∑ r ∈ S, ‖a r‖) ≤ R*(K*(Real.log (R*U))^B) := by
    nlinarith [ha]
  have hb := hbound S a R U T (R*(K*(Real.log (R*U))^B)) hRp hU hT hS hA
  rw [typeI_level_mass_scaling hRp hUp] at hb
  apply hb.trans
  have hmain := typeI_principal_log_bound hX hRp hRX hδ.le B (hlog _ hX)
  have hpow := Real.rpow_le_rpow_of_exponent_le hX
    (show 1/2+3*δ ≤ 1/2+ε by linarith)
  have hmain' : (R*U)^(1/2+δ)*R^(3/4+δ)*(Real.log (R*U))^B ≤
      L*(R*U)^(1/2+ε)*R^(3/4:ℝ) := hmain.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hL.le)
          (Real.rpow_nonneg hRp.le _))
  calc
    _ = (C*2^(1/4+2*δ)*K)*
        ((R*U)^(1/2+δ)*R^(3/4+δ)*(Real.log (R*U))^B)*Real.sqrt T+
        (E*K)*(R*U)^(5/6:ℝ)*(Real.log (R*U))^B/T^D := by ring
    _ ≤ (C*2^(1/4+2*δ)*K)*
        (L*(R*U)^(1/2+ε)*R^(3/4:ℝ))*Real.sqrt T+
        (E*K)*(R*U)^(5/6:ℝ)*(Real.log (R*U))^B/T^D := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmain' (by positivity)) (Real.sqrt_nonneg _)) le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
