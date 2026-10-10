import OAI.Analysis.KadisonKastler.RealThresholdSelection
import OAI.Analysis.KadisonKastler.FiniteThresholdEstimate
import OAI.Analysis.KadisonKastler.ProjectionCommutatorEnergy

namespace OAI

/-! # Selecting one finite spectral cut with small displacement and a gap -/

namespace KadisonKastler

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

omit [CompleteSpace H] in
theorem finiteThresholdProjection_commute
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ) (t : ℝ) :
    Commute (finiteThresholdProjection P c t) (finiteThresholdProjection Q d t) := by
  unfold finiteThresholdProjection
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((hc i j).smul_left _).smul_right _

theorem thresholdDifference_zero_outside {x y t : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∉ Set.Icc (-1 : ℝ) 1) : thresholdDifference x y t = 0 := by
  by_cases hl : t < -1
  · simp [thresholdDifference,hl.trans_le hx.1,hl.trans_le hy.1]
  · have hr : 1 < t := by
      by_contra h
      exact ht ⟨le_of_not_gt hl,le_of_not_gt h⟩
    simp [thresholdDifference,not_lt.mpr (hx.2.trans hr.le),not_lt.mpr (hy.2.trans hr.le)]

theorem exists_finite_spectral_cut
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ)
    (hcr : ∀ i, c i ∈ Set.Icc (-1 : ℝ) 1) (hdr : ∀ j, d j ∈ Set.Icc (-1 : ℝ) 1)
    (ξ η : H) (hη : ‖η‖ = 1) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (hsmall : ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ * ‖ξ‖ <
      δ * (‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) η‖ ^ 2 / 2 - 2 * b)) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2 ≤ δ ∧
      b ≤ ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) η‖ ^ 2 := by
  let f (ζ : H) (t : ℝ) :=
    ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ζ‖ ^ 2
  have hf (ζ : H) : Integrable (f ζ) := by
    have he (t : ℝ) := finiteThresholdProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc c d t ζ
    simp_rw [show f ζ = fun t => ∑ a : ι × κ, ‖(P a.1 * Q a.2) ζ‖ ^ 2 *
      thresholdDifference (c a.1) (d a.2) t ^ 2 from funext he]
    exact integrable_finsetSum _ (fun a _ =>
      (thresholdDifference_sq_integrable (c a.1) (d a.2)).const_mul _)
  have hs (ζ : H) (t : ℝ) (ht : t ∉ Set.Icc (-1 : ℝ) 1) : f ζ t = 0 := by
    change ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ζ‖ ^ 2 = 0
    rw [finiteThresholdProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
    apply Finset.sum_eq_zero
    intro a _
    rw [thresholdDifference_zero_outside (hcr a.1) (hdr a.2) ht]
    ring
  have hbound (t : ℝ) : f η t ≤ 1 := by
    have he := pairedProjectionCut_energy (finiteThresholdProjection_isProjection P hP hPo c t)
      (finiteThresholdProjection_isProjection Q hQ hQo d t)
      (finiteThresholdProjection_commute P Q hc c d t) η
    rw [hη] at he
    change ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) η‖ ^ 2 ≤ 1
    nlinarith [sq_nonneg ‖pairedProjectionCut (finiteThresholdProjection P c t)
      (finiteThresholdProjection Q d t) η‖]
  apply exists_good_real_threshold (f ξ) (f η) (hf ξ) (hf η) (hs ξ) (hs η)
    (fun _ => sq_nonneg _) hbound _ _ δ b hδ hb
    (finiteThresholdProjection_integral_le P Q hP hQ hPo hQo hPt hQt hc c d ξ) _ hsmall
  have hrange (i : ι) (j : κ) : |c i-d j| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [(hcr i).1,(hcr i).2,(hdr j).1,(hdr j).2]
  have he := finiteThresholdProjection_integral_lower P Q hP hQ hPo hQo hPt hQt hc c d η hrange
  change _ ≤ ∫ t, f η t
  dsimp [f]
  simp only [Complex.coe_smul] at he ⊢
  linarith

end

end KadisonKastler

end OAI
