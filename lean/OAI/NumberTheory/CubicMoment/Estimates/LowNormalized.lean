import OAI.NumberTheory.CubicMoment.Estimates.LowLocalizedIntegral
import OAI.NumberTheory.CubicMoment.Estimates.LowLogRoot
import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinearValue

namespace OAI

/-! Logarithmic cell width and height threshold for the low-height range. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem low_localized_integral_log_saving
    (hpnt : PrimaryPrimePNT)
    {C Mα Mβ M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (hM : 0 ≤ M) (j dα dβ a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T H : ℝ),
      (65536:ℝ)^2 ≤ Z →
      2*Z^(3/2:ℝ) ≤ A → A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ H →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ S, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ S, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ H) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖heightBilinearValue P S α β h X₀ T‖ ≤
        K*H*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨d,hfamily⟩ := low_localized_height_integral_bound hpnt hMV hC hHuxley
  let D := a+2*(j+1)+dα+dβ
  let q := D*(d+4)+(2*(j+1)+dα)
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily q
  let B := Real.sqrt (Mα*Mβ)+Real.sqrt (Mα*M^2)
  refine ⟨2*K*(B+1),Ct+2*D,by dsimp [B]; positivity,?_⟩
  intro P S α β Z A X₀ T H hZ hA hAu hX hT hH hP hS hβ hea heb h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hL8 := low_large_log hZ
  let L := 1+Real.log Z
  let J := L^D
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  have hZp : 0 < Z := by nlinarith
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hD1 : 1 ≤ D := by dsimp [D]; omega
  have hJ : 8 ≤ J := hL8.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 hD1)
  have hJ1 : 1 ≤ J := by linarith
  have hT0 : L^Ct ≤ T := (pow_le_pow_right₀ hL1 (by omega : Ct ≤ Ct+2*D)).trans hT
  have hTJ : J^2 ≤ T := by
    dsimp [J]
    rw [←pow_mul]
    exact (pow_le_pow_right₀ hL1 (by omega : D*2 ≤ Ct+2*D)).trans hT
  have hTp : 0 < T := (pow_pos hLp Ct).trans_le hT0
  have hJle : J ≤ T := (le_self_pow₀ hJ1 (by norm_num : 2 ≠ 0)).trans hTJ
  have hratio : J*(J/T)^2 ≤ 1 := by
    have h1 : J/T ≤ 1 := (div_le_one hTp).mpr hJle
    have h2 : J^2/T ≤ 1 := (div_le_one hTp).mpr hTJ
    have hm : (J/T)*(J^2/T) ≤ 1 := by
      calc
        _ ≤ 1*(J^2/T) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ 1 := by simpa using h2
    convert hm using 1
    ring
  have hdiag := low_diagonal_root_log_saving hAp hZp hLp hMα hMβ
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (j+1) dα dβ a hAu hea heb
  have herr := low_remainder_root_log_saving (M := M) hAp hZp hLp hMα
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (j+1) dα d D hea
  have hroot : Real.sqrt (A/J)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)*Real.sqrt (∑ n ∈ S, ‖β n‖^2)+
      J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^q)*Real.sqrt (∑ n ∈ P, ‖α n‖^2) ≤
      B*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
    have hb := add_le_add hdiag herr
    have he : Real.sqrt (A/J)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)*Real.sqrt (∑ n ∈ S, ‖β n‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^q)*Real.sqrt (∑ n ∈ P, ‖α n‖^2) ≤
        B*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^(j+1) := by
      convert hb using 1
      dsimp [J,D,q,B,L]
      ring
    exact he.trans (div_le_div_of_nonneg_left (by dsimp [B]; positivity)
      (pow_pos hLp j) (pow_le_pow_right₀ hL1 (by omega : j ≤ j+1)))
  have hb := hbound J hJ P S α β Z A X₀ T M H hZ hA hX hT0 hM hH hP hS hβ
    h hi hd hi' hd' hi'' hh hs hh2 hs2
  apply hb.trans
  have hr := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ K*(1+J*(J/T)^2)*H by positivity)
  apply hr.trans
  have hc : K*(1+J*(J/T)^2)*B ≤ 2*K*(B+1) := by
    have hB : 0 ≤ B := by dsimp [B]; positivity
    nlinarith [mul_nonneg hK.le hB,mul_le_mul_of_nonneg_left hratio (mul_nonneg hK.le hB)]
  have hc' := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ H*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j by positivity)
  convert hc' using 1 <;> ring

end CubicFirstMoment

end

end OAI
