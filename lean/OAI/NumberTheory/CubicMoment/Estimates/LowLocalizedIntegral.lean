import OAI.NumberTheory.CubicMoment.Estimates.LowNearIntegrated
import OAI.NumberTheory.CubicMoment.Estimates.LowFarHeight
import OAI.NumberTheory.CubicMoment.Estimates.LogLocalizedIntegral

namespace OAI

/-! The literal height integral, with separate low-height diagonal and error.
The derivative degree is chosen before the desired logarithmic saving. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem low_localized_height_integral_bound
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M H : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M → 0 ≤ H →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ H) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖(T:ℂ)⁻¹*(∑ a ∈ P, ∑ b ∈ S, (α a*β b*gauss (a*b))*
        heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀))‖ ≤
      K*(1+J*(J/T)^2)*H*(Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*
        Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)) := by
  obtain ⟨dn,hnear⟩ := low_near_logCell_integrated_bound hpnt hMV hC hHuxley
  obtain ⟨df,hfar⟩ := low_far_logCell_integrated_bound hpnt hMV hC hHuxley
  refine ⟨dn+df,?_⟩
  intro q
  obtain ⟨Kn,Cn,hKn,hn⟩ := hnear q
  obtain ⟨Kf,Cf,hKf,hf⟩ := hfar q
  refine ⟨Kn+Kf,Cn+Cf,by positivity,?_⟩
  intro J hJ P S α β Z A X₀ T M H hZ hA hX hT hM hH hP hS hβ h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hJ1 : 1 ≤ J := by linarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hAp : 0 < A := lt_of_lt_of_le
    (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hL1 : 1 ≤ 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hTn : (1+Real.log Z)^Cn ≤ T :=
    (pow_le_pow_right₀ hL1 (by omega : Cn ≤ Cn+Cf)).trans hT
  have hTf : (1+Real.log Z)^Cf ≤ T :=
    (pow_le_pow_right₀ hL1 (by omega : Cf ≤ Cn+Cf)).trans hT
  let D := Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)
  let E := fun d : ℕ => J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
    Real.sqrt (∑ a ∈ P, ‖α a‖^2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE (d : ℕ) : 0 ≤ E d := by dsimp [E]; positivity
  have hmono (d : ℕ) (hd : d ≤ dn+df) : E d ≤ E (dn+df) := by
    dsimp [E]
    gcongr
  let Q := D+E (dn+df)
  have hQ : 0 ≤ Q := add_nonneg hD (hE _)
  have hn' : ‖(T:ℂ)⁻¹*∑ e ∈ nearLogNormCells P S J A (Z/2) X₀,
      logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤ Kn*H*Q := by
    have hb := hn J hJ P S α β Z A X₀ T M H hZ hA hX hTn hM hH hP hS hβ h hi hh hs
    apply hb.trans
    exact mul_le_mul_of_nonneg_left (add_le_add (le_refl D) (hmono dn (by omega)))
      (mul_nonneg hKn.le hH)
  have hf' : ‖(T:ℂ)⁻¹*∑ e ∈ farLogNormCells P S J A (Z/2) X₀,
      logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤ Kf*(J/T)^2*H*J*Q := by
    have hb := hf J hJ P S α β Z A X₀ T M H hZ hA hX hTf hM hH hP hS hβ
      h hi hd hi' hd' hi'' hh2 hs2
    apply hb.trans
    have he := (hmono df (by omega)).trans
      (le_mul_of_one_le_left (hE _) hJ1)
    have hb' := mul_le_mul_of_nonneg_left (add_le_add (le_refl (J*D)) he)
      (show 0 ≤ Kf*(J/T)^2*H by positivity)
    dsimp [D,E,Q] at hb' ⊢
    nlinarith only [hb']
  rw [logCellHeightSum_partition P S α β J A (Z/2) X₀ h,mul_add]
  apply (norm_add_le _ _).trans ((add_le_add hn' hf').trans ?_)
  have hx : 0 ≤ J*(J/T)^2 := by positivity
  have hb : Kn+Kf*(J*(J/T)^2) ≤ (Kn+Kf)*(1+J*(J/T)^2) := by
    nlinarith [mul_nonneg hKn.le hx]
  have hb' := mul_le_mul_of_nonneg_right hb (mul_nonneg hH hQ)
  dsimp [Q,D,E] at hb' ⊢
  nlinarith only [hb']

end CubicFirstMoment

end

end OAI
