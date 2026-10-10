import OAI.NumberTheory.CubicMoment.Decomposition.StoppedModelNorm
import OAI.NumberTheory.CubicMoment.Estimates.CubeMassComparison
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! The finite cube density equals the true squarefree model mass for
actual bounded stopped coefficients, with arbitrary logarithmic accuracy. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_cube_mass_log_saving {ξ κ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hκ : 0 < κ) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦpos : tsupport Φ ⊆ Set.Ioi 0) (hΦ' : ContDiff ℝ ∞ Φ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein) (b u A : ℝ),
      X^κ ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
      ‖(finiteSieveDensity (squarefreeDivisorTruncation ((Real.log X)^(2*k))):ℂ)*
          cubeModelTerm S β u Φ A-
        ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  let hv : UniformLogWeights (fun _ : Unit => Φ) := uniformLogWeights_constant Φ hΦ hΦpos hΦ'
  obtain ⟨C,hC,hmass⟩ := hv.cubeModelTerm_mass_error
  obtain ⟨E,hE,hmodel⟩ := stopped_model_norm (ι := ι) hξ hξz
  refine ⟨2*C*E^2,by positivity,?_⟩
  filter_upwards [hmodel,negative_power_log_saving (show 0 < κ*(3/8) by positivity) k,
    (tendsto_rpow_atTop hκ).eventually_ge_atTop 1,eventually_ge_atTop (Real.exp 1)]
    with X hmodel hdecay hlarge hX
  intro W hW selected e b u A hbX hbXhi hAlo
  dsimp only
  have hb1 : 1 ≤ b := hlarge.trans hbX
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hAlo
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  have he : ‖dispersionModel S β u‖^2 ≤ E^2*b^(5/3:ℝ) := by
    have hm := pow_le_pow_left₀ (_root_.norm_nonneg _) (hmodel W hW selected e b 0 u hbp hbXhi) 2
    apply hm.trans_eq
    rw [mul_pow,←Real.rpow_mul_natCast hbp.le]
    norm_num
  have ha : A^(-(1/4:ℝ)) ≤ 1/(Real.log X)^k := by
    calc
      _ ≤ (b^(3/2:ℝ))^(-(1/4:ℝ)) := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hbp _) hAlo (by norm_num)
      _ = b^(-(3/8:ℝ)) := by rw [←Real.rpow_mul hbp.le]; norm_num
      _ ≤ (X^κ)^(-(3/8:ℝ)) := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hXp _) hbX (by norm_num)
      _ = X^(-(κ*(3/8))) := by rw [←Real.rpow_mul hXp.le]; congr 1; ring
      _ ≤ 1/(1+Real.log X)^k := hdecay
      _ ≤ _ := one_div_le_one_div_of_le (pow_pos hLp k)
        (pow_le_pow_left₀ hLp.le (by linarith) k)
  have hd : ((Real.log X)^(2*k))^(-(1/2:ℝ)) = 1/(Real.log X)^k := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
    have he : ((2*k:ℕ):ℝ)*(-(1/2:ℝ)) = -(k:ℝ) := by push_cast; ring
    rw [he,Real.rpow_neg hLp.le,Real.rpow_natCast,one_div]
  have hs : A^(5/12:ℝ)+A^(2/3:ℝ)*((Real.log X)^(2*k))^(-(1/2:ℝ)) ≤
      2*A^(2/3:ℝ)/(Real.log X)^k := by
    rw [hd,show A^(5/12:ℝ) = A^(2/3:ℝ)*A^(-(1/4:ℝ)) by
      rw [←Real.rpow_add hAp]; norm_num]
    exact (add_le_add (mul_le_mul_of_nonneg_left ha (by positivity)) le_rfl).trans_eq (by ring)
  have hb := hmass () S β u A ((Real.log X)^(2*k)) hA1 (one_le_pow₀ hL1)
  apply hb.trans
  calc
    _ ≤ C*(E^2*b^(5/3:ℝ))*(2*A^(2/3:ℝ)/(Real.log X)^k) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he hC.le) hs (by positivity) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
