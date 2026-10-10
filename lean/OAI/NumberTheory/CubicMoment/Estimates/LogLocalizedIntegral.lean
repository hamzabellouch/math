import OAI.NumberTheory.CubicMoment.Estimates.NearLogCellIntegrated

namespace OAI

/-! Near and far cells reassemble the original Gauss height integral.
This is the high-height, arbitrary-coefficient localization estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma logCellHeightSum_partition (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (h : ℝ → ℂ) :
    (∑ a ∈ P, ∑ b ∈ S, (α a*β b*gauss (a*b))*
      heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀)) =
      (∑ e ∈ nearLogNormCells P S J A B X₀, logCellHeightSum P S α β J A B X₀ e h)+
      (∑ e ∈ farLogNormCells P S J A B X₀, logCellHeightSum P S α β J A B X₀ e h) := by
  rw [sum_near_farLogNormCells]
  let f := fun a b : Eisenstein => (α a*β b*gauss (a*b))*
    heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀)
  have hp := logNormCell_bilinear_partition P S J A B f
  calc
    _ = ∑ i ∈ P.image (logNormCell J A), ∑ j ∈ S.image (logNormCell J B),
        logCellHeightSum P S α β J A B X₀ (i,j) h := hp
    _ = _ := (Finset.sum_product (P.image (logNormCell J A)) (S.image (logNormCell J B))
      (fun e => logCellHeightSum P S α β J A B X₀ e h)).symm

theorem localized_height_integral_bound
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M : ℝ),
      65536 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ M) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ M) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖(T:ℂ)⁻¹*(∑ a ∈ P, ∑ b ∈ S, (α a*β b*gauss (a*b))*
        heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀))‖ ≤
        K*(1+J*(J/T)^2)*M*(Real.sqrt (A/J)+
          Real.sqrt (J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)))*
            Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨dn,Kn,hKn,hn⟩ := near_logCell_integrated_bound hMV hC hHuxley
  obtain ⟨df,Kf,hKf,hf⟩ := far_logCell_integrated_bound hMV hC hHuxley
  refine ⟨dn+df,Kn+Kf,by positivity,?_⟩
  intro J hJ P S α β Z A X₀ T M hZ hA hX hT hM hP hS h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hJ1 : 1 ≤ J := by linarith
  have hZp : 0 < Z := by linarith
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  let Q := Real.sqrt (A/J)+Real.sqrt (J^(dn+df)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ))
  let E := Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpow (d : ℕ) (hd : d ≤ dn+df) :
      Real.sqrt (A/J)+Real.sqrt (J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)) ≤ Q := by
    apply add_le_add (le_refl _)
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hJ1 hd) (by positivity)) (by positivity)
  have hnear := hn J hJ P S α β Z A X₀ T M hZ hA hX hT hM hP hS h hi hh hs
  have hfar := hf J hJ P S α β Z A X₀ T M hZ hA hX hT hM hP hS h hi hd hi' hd' hi'' hh2 hs2
  have hn' : ‖(T:ℂ)⁻¹*∑ e ∈ nearLogNormCells P S J A (Z/2) X₀,
      logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤ Kn*M*Q*E := by
    apply hnear.trans
    have hb := mul_le_mul_of_nonneg_left (hpow dn (by omega)) (mul_nonneg hKn.le hM)
    have hb' := mul_le_mul_of_nonneg_right hb hE
    dsimp [E] at hb'
    nlinarith only [hb']
  have hf' : ‖(T:ℂ)⁻¹*∑ e ∈ farLogNormCells P S J A (Z/2) X₀,
      logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤ Kf*(J/T)^2*M*J*Q*E := by
    apply hfar.trans
    have hb := mul_le_mul_of_nonneg_left (hpow df (by omega))
      (show 0 ≤ Kf*(J/T)^2*M*J by positivity)
    have hb' := mul_le_mul_of_nonneg_right hb hE
    dsimp [E] at hb'
    nlinarith only [hb']
  rw [logCellHeightSum_partition P S α β J A (Z/2) X₀ h,mul_add]
  apply (norm_add_le _ _).trans ((add_le_add hn' hf').trans ?_)
  have hx : 0 ≤ J*(J/T)^2 := by positivity
  have hb : Kn+Kf*(J*(J/T)^2) ≤ (Kn+Kf)*(1+J*(J/T)^2) := by
    nlinarith [mul_nonneg hKn.le hx]
  have hb' := mul_le_mul_of_nonneg_right hb (mul_nonneg (mul_nonneg hM hQ) hE)
  dsimp [Q,E] at hb' ⊢
  nlinarith only [hb']

end CubicFirstMoment

end

end OAI
