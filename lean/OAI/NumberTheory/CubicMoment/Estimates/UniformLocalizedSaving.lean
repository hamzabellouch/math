import OAI.NumberTheory.CubicMoment.Estimates.LocalizedLogSaving

namespace OAI

/-! Choose the analytic power-width before any coefficient losses or
requested logarithmic savings. This order is needed to fix the stopping
parameters before the finite prime arity is known. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem localized_integral_log_saving_uniform
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (Mα Mβ : ℝ), 0 ≤ Mα → 0 ≤ Mβ →
      ∀ (j dα dβ : ℕ),
    ∃ K Z₀ : ℝ, 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T M : ℝ),
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → 0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ a ∈ P, ‖α a‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ M) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ M) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖heightBilinearValue P S α β h X₀ T‖ ≤
        K*M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨γ,K,Z₀,hγ,hK,hbound⟩ := localized_integral_power_saving hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro Mα Mβ hMα hMβ j dα dβ
  obtain ⟨H,hH,hlog⟩ := log_power_normalization_bound (2*j+dα+dβ)
    (s := 2*γ/3) (by positivity)
  let K' := Real.sqrt (Mα*(K^2*Mβ*H))+1
  refine ⟨K',max Z₀ 65536,by dsimp [K']; positivity,?_⟩
  intro P S α β Z A X₀ T M hZ hA hAu hX hT hM hP hS hea heb h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hZ1 : 1 ≤ Z := by have := (le_max_right Z₀ 65536).trans hZ; linarith
  have hZp : 0 < Z := zero_lt_one.trans_le hZ1
  have hLp : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hb := hbound P S α β Z A X₀ T M ((le_max_left _ _).trans hZ)
    hA hAu hX hT hM hP hS h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hr := localized_root_log_saving hAp hZ1 hK.le hMα hMβ hH j dα dβ
    (hlog Z hZ1) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hea heb
  calc
    _ ≤ M*(K*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*γ/3))*
        Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)) := by
      convert hb using 1; ring
    _ ≤ M*(Real.sqrt (Mα*(K^2*Mβ*H))*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j) :=
      mul_le_mul_of_nonneg_left hr hM
    _ ≤ K'*M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
      dsimp [K']
      have hp : 0 ≤ M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by positivity
      calc
        _ = Real.sqrt (Mα*(K^2*Mβ*H))*(M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j) := by ring
        _ ≤ (Real.sqrt (Mα*(K^2*Mβ*H))+1)*(M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j) :=
          mul_le_mul_of_nonneg_right (by linarith) hp
        _ = _ := by ring


end CubicFirstMoment

end

end OAI
