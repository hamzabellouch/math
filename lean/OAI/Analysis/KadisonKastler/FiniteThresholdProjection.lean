import OAI.Analysis.KadisonKastler.JointProjectionEnergy
import OAI.Analysis.KadisonKastler.ThresholdCutIntegral

namespace OAI

/-! # Projection-valued threshold cuts of finite spectral sums -/

namespace KadisonKastler

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

def finiteThresholdProjection (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) : H →L[ℂ] H :=
  ∑ i, ((if t < c i then 1 else 0 : ℝ) : ℂ) • P i

theorem finiteThresholdProjection_isProjection
    (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i * P j = 0) (c : ι → ℝ) (t : ℝ) :
    IsStarProjection (finiteThresholdProjection P c t) := by
  classical
  have he : finiteThresholdProjection P c t = ∑ i ∈ univ.filter (fun i => t < c i), P i := by
    simp only [finiteThresholdProjection,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t < c i <;> simp [hi]
  rw [he]
  exact isStarProjection_sum_orthogonal _ P (fun i _ => hP i) (fun i _ j _ hij => ho i j hij)

theorem finiteThresholdProjection_gap_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ) (t : ℝ) (ξ : H) :
    ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 *
        thresholdDifference (c a.1) (d a.2) t ^ 2 := by
  rw [finiteThresholdProjection,finiteThresholdProjection,
    jointProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
  apply Finset.sum_congr rfl
  intro a _
  have he : ‖((if t < c a.1 then 1 else 0 : ℝ) : ℂ) -
      ((if t < d a.2 then 1 else 0 : ℝ) : ℂ)‖ ^ 2 =
      thresholdDifference (c a.1) (d a.2) t ^ 2 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rfl
  rw [he,mul_comm]

theorem finiteThresholdProjection_integrated_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∫ t, ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2) =
      ∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 * |c a.1-d a.2| := by
  simp_rw [finiteThresholdProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
  exact integral_weighted_thresholdDifference_sq univ _ _ _

end

end KadisonKastler

end OAI
