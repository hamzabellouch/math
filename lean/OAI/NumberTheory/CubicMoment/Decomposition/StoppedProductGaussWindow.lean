import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductProfile
import OAI.NumberTheory.CubicMoment.Estimates.LowNormalized

namespace OAI

/-! A whole signed Mellin-height window for a fixed Schwartz multiplier.
This is an application of the proved localized Gauss estimate, retaining
its coefficient energies and its lower length/height ranges. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem schwartz_gauss_window_log_saving
    (hpnt : PrimaryPrimePNT) {C Mα Mβ M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (hM : 0 ≤ M)
    (j dα dβ a : ℕ) (f : SchwartzMap ℝ ℂ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P B : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ B, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ B, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ B, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖∫ t : ℝ, (f t*heightWindow T t)*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist t (c*b)‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(T*(1+Real.log Z)^j) := by
  obtain ⟨K₀,Ct,hK₀,hbound⟩ := low_localized_integral_log_saving hpnt hMV hC
    hHuxley hMα hMβ hM j dα dβ a
  obtain ⟨K₂,hK₂,hsecond⟩ := schwartzHeightWindow_second_bound f
  let D := 1+SchwartzMap.seminorm ℝ 2 0 f+K₂
  have hD : 0 < D := by dsimp [D]; have := apply_nonneg (SchwartzMap.seminorm ℝ 2 0) f; linarith
  refine ⟨K₀*D,Ct,mul_pos hK₀ hD,?_⟩
  intro P B α β Z A X₀ T hZ hA hAu hX₀ hT hP hB hβ hαE hβE
  have hZ1 : 1 ≤ Z := by nlinarith
  have hT0 : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) Ct).trans_le hT
  let h := schwartzHeightWindow f T
  have hs := schwartzHeightWindow_derivatives f hT0
  have hn (t : ℝ) : ‖h t‖ ≤ D/T :=
    (schwartzHeightWindow_norm_bound f hT0 t).trans
      (div_le_div_of_nonneg_right (by dsimp [D]; linarith) hT0.le)
  have hn₂ (t : ℝ) : ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ D/T :=
    (hsecond T hT0 t).trans
      (div_le_div_of_nonneg_right (by dsimp [D]; have := apply_nonneg (SchwartzMap.seminorm ℝ 2 0) f; linarith) hT0.le)
  have hb := hbound P B α β Z A X₀ T (D/T) hZ hA hAu hX₀ hT (by positivity)
    hP hB hβ hαE hβE h hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 hn
    (schwartzHeightWindow_zero f hT0) hn₂ (schwartzHeightWindow_second_zero f hT0)
  have he : heightBilinearValue P B α β h X₀ T =
      ∫ t : ℝ, (f t*heightWindow T t)*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist t (c*b) := by
    rw [heightBilinearValue_eq_integral P B α β h hs.1,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [h,schwartzHeightWindow]
    have hc : (T:ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
    field_simp
  rw [he] at hb
  convert hb using 1; ring

end CubicFirstMoment

end

end OAI
