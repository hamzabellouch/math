import OAI.NumberTheory.CubicMoment.Decomposition.StoppedOrdinaryLowSaving
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralStoppedProductLowSaving

namespace OAI

/-! The actual ordinary side lengths and actual distinguished partition
weights satisfy every analytic parameter condition of the stopped bound. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem ordinary_stopped_low_kernel_bound_actual (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C ξ ρ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (k Ct : ℕ) :
    ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (N : ℕ) (d : Fin i → Fin N) (A b H : ℝ),
      X/16 ≤ A*b → A*b ≤ 16*X →
      X^(7/20:ℝ) ≤ b → b ≤ X^(39/100:ℝ) → 0 < H →
      ∀ (j q h : ℕ) (Z Q : ℝ) (early : Bool), j ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower ρ X h) →
      ∀ (E₀ U P : Finset Eisenstein) (remaining : Eisenstein → Prop),
      (∀ e ∈ E₀, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      let S := stoppedIntervalSupport (Fin i) X (b/2) b 1
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j q h Z Q early)
      ‖∑ a ∈ P, ∑ b ∈ S, stoppedAlpha E₀ U primeDetectorCutoff (X^ξ) remaining a*β b*
        centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b)‖ ≤
        K*X^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨V,hV,hweights⟩ := distinguishedStoppingWeights_uniform
  obtain ⟨d₀,G,K,hK,hbound⟩ := stopped_product_low_log_saving_actual (ι := Fin i)
    (κ := 1/4) (E := 0) (F := 1) (J := 1)
    hpnt hSW hMV hC hHuxley  hGamma hξ hξz (by norm_num) (by norm_num) (by norm_num)
    (dispersionCutoff 4) (dispersionCutoff_nonneg 4) (dispersionCutoff_complex_compact 4)
    (dispersionCutoff_positive_support 4) (dispersionCutoff_complex_smooth 4)
    (fun x hx => by rw [dispersionCutoff_one ⟨hx.1,by linarith [hx.2]⟩])
    (RΦ := 5) (fun x hx => dispersionCutoff_high (by linarith))
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth k Ct
  refine ⟨G,K*(16:ℝ)^(5/6:ℝ),by positivity,?_⟩
  filter_upwards [hbound,eventually_stopped_actual_range (15*(2*(k+Ct)+d₀)),
    eventually_fixed_stopping_mesh hρ hρ₂,
    Real.tendsto_log_atTop.eventually_ge_atTop (1+V),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop 2,
    eventually_gt_atTop (1:ℝ)] with X hb hr hw hVX htwo hX
  intro N d A b H hp hp' hblo hbhi hH j q h Z Q early hj hrough E₀ U P remaining hE₀ hP
  dsimp only
  have hXp : 0 < X := zero_lt_one.trans hX
  have hbp : 0 < b := (Real.rpow_pos_of_pos hXp _).trans_le hblo
  have hbκ : X^(1/4:ℝ) ≤ b :=
    (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (1/4:ℝ) ≤ 7/20)).trans hblo
  have hpow : X^(39/100:ℝ) ≤ X^(1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  have hbX : b ≤ X := hbhi.trans (by simpa only [Real.rpow_one] using hpow)
  obtain ⟨hAlo,hAhi⟩ := hr A b hp hp' hblo hbhi
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le
    ((le_mul_of_one_le_left (Real.rpow_nonneg hbp.le _) (by norm_num : (1:ℝ) ≤ 2)).trans hAlo)
  have hh := hb (ρ-1) b V A X H hw.1 hw.2.1 hw.2.2 (htwo.trans hbκ) hbκ hbX hXp
    hV (by simpa only [Real.rpow_one] using hVX) hH
    (distinguishedStoppingWeights d) (hweights i N d).1 (hweights i N d).2.1
    (hweights i N d).2.2 hAlo hAhi 1 one_ne_zero
    (by simp only [norm_one_eq,Real.rpow_zero,le_refl]) j q h Z Q early hj
    (by simpa only [show 1+(ρ-1)=ρ by ring] using hrough) E₀ U P primeDetectorCutoff (X^ξ)
    remaining hE₀ (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) hP
  simp only [show 1+(ρ-1)=ρ by ring] at hh
  apply hh.trans
  have hscale : A^(5/6:ℝ)*b^(5/6:ℝ) ≤ (16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ) := by
    rw [←Real.mul_rpow hAp.le hbp.le,←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hXp.le]
    exact Real.rpow_le_rpow (mul_nonneg hAp.le hbp.le) hp' (by norm_num)
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Real.log_pos hX).le _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hK.le

end CubicFirstMoment

end

end OAI
