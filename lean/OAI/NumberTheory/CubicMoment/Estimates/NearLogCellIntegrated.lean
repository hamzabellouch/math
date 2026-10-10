import OAI.NumberTheory.CubicMoment.Estimates.CellHeightIntegral

namespace OAI

/-! The actual near cells in the normalized, weighted height integral. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem near_logCell_integrated_bound
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M : ℝ),
      65536 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ∀ h : ℝ → ℂ, Integrable h → (∀ t, ‖h t‖ ≤ M) →
      (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      ‖(T:ℂ)⁻¹*∑ e ∈ nearLogNormCells P S J A (Z/2) X₀,
        logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤
        K*M*(Real.sqrt (A/J)+Real.sqrt (J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)))*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨d,K,hK,hnear⟩ := near_logCell_height_bound hMV hC hHuxley
  refine ⟨d,K,hK,?_⟩
  intro J hJ P S α β Z A X₀ T M hZ hA hX hT hM hP hS h hi hh hs
  have hZp : 0 < Z := by linarith
  have hTp : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  let E := nearLogNormCells P S J A (Z/2) X₀
  let f := fun t : ℝ => ∑ e ∈ E, logCellPolynomial P S α β J A (Z/2) e t
  let w := fun t : ℝ => h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)
  have hf : Continuous f := continuous_finsetSum E (fun e _ =>
    logCellPolynomial_continuous P S α β J A (Z/2) e)
  have hw : ∀ t, ‖w t‖ ≤ M := by
    intro t
    have hp : ‖Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    simpa only [w,norm_mul,hp,mul_one] using hh t
  have hws : ∀ t, t ∉ dyadicHeightSupport T → w t = 0 := by
    intro t ht
    simp only [w,hs t ht,zero_mul]
  have hb := normalized_dyadicWeightIntegral_bound f w hf hTp hM hw hws
  have hn := hnear J hJ P S α β Z A (Z/2) X₀ T 0 hZ hA (by positivity) hX hT hP hS
  simp only [zero_add] at hn
  rw [finite_logCellHeightSum_integral P S α β J A (Z/2) X₀ E h hi]
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left hn hM
  convert hm using 1
  ring

end CubicFirstMoment

end

end OAI
