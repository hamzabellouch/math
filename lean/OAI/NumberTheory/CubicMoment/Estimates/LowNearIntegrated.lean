import OAI.NumberTheory.CubicMoment.Estimates.CellHeightIntegral
import OAI.NumberTheory.CubicMoment.Estimates.LowNearHeight

namespace OAI

/-! The actual near cells in the normalized, weighted height integral. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem low_near_logCell_integrated_bound
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M H : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ → (1+Real.log Z)^Ct ≤ T → 0 ≤ M → 0 ≤ H →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      ∀ h : ℝ → ℂ, Integrable h → (∀ t, ‖h t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      ‖(T:ℂ)⁻¹*∑ e ∈ nearLogNormCells P S J A (Z/2) X₀,
        logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤
        K*H*(Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
          J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
            Real.sqrt (∑ a ∈ P, ‖α a‖^2)) := by
  obtain ⟨d,hfamily⟩ := low_near_logCell_height_bound hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro q
  obtain ⟨K,Ct,hK,hnear⟩ := hfamily q
  refine ⟨K,Ct,hK,?_⟩
  intro J hJ P S α β Z A X₀ T M H hZ hA hX hT hM hH hP hS hβ h hi hh hs
  have hZp : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hL _).trans_le hT
  let E := nearLogNormCells P S J A (Z/2) X₀
  let f := fun t : ℝ => ∑ e ∈ E, logCellPolynomial P S α β J A (Z/2) e t
  let w := fun t : ℝ => h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)
  have hf : Continuous f := continuous_finsetSum E (fun e _ =>
    logCellPolynomial_continuous P S α β J A (Z/2) e)
  have hw : ∀ t, ‖w t‖ ≤ H := by
    intro t
    have hp : ‖Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    simpa only [w,norm_mul,hp,mul_one] using hh t
  have hws : ∀ t, t ∉ dyadicHeightSupport T → w t = 0 := by
    intro t ht
    simp only [w,hs t ht,zero_mul]
  have hb := normalized_dyadicWeightIntegral_bound f w hf hTp hH hw hws
  have hn := hnear J hJ P S α β Z A X₀ T M 0 hZ hA hX hT hM hP hS hβ
  simp only [zero_add] at hn
  rw [finite_logCellHeightSum_integral P S α β J A (Z/2) X₀ E h hi]
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left hn hH
  convert hm using 1
  ring

end CubicFirstMoment

end

end OAI
