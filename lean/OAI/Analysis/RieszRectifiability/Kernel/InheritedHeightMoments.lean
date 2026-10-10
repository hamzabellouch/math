import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxContainment
import OAI.Analysis.RieszRectifiability.Kernel.GlobalSingularHeight

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem dyadic_annulus_subset_bounded_box {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (R : ℝ) (M : ℕ) (hM : 2 * R * ((Q : ℝ) + 1) ≤ M) (k : ℕ) :
    dyadicAnnulus (e 0) R k ⊆ boundedProjectionRegion π (e 0) K (M * 2 ^ k) := by
  have hinner : R * (2 : ℝ) ^ (k + 1) ≤ planeBoxInnerRadius Q (M * 2 ^ k) := by
    unfold planeBoxInnerRadius
    apply (le_div_iff₀ (by positivity : 0 < (Q : ℝ) + 1)).mpr
    push_cast
    rw [pow_succ]
    have hm := mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ (2 : ℝ) ^ k)
    nlinarith
  exact (dyadicAnnulus_subset_ball (e 0) R k).trans ((ball_subset_ball hinner).trans
    (ball_subset_boundedProjectionRegion e π K Q hπ hleft (M * 2 ^ k)))

theorem dyadic_bounded_box_subset_ball {ι : Type*} {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (M k : ℕ) :
    boundedProjectionRegion π a K (M * 2 ^ k) ⊆
      ball a ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k) := by
  intro x hx
  apply (ball_subset_ball ?_) hx.2
  unfold planeBoxOuterRadius
  push_cast
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  nlinarith [K.coe_nonneg]

theorem inherited_annular_second_moments {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (R : ℝ) (M : ℕ) (hM : 2 * R * ((Q : ℝ) + 1) ≤ M)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (w : ℕ → Ambient d → ℝ) (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2 (ν.restrict (boundedProjectionRegion π (e 0) K H)))
    (hlimit : ∀ H, Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (hw : ∀ k j, MemLp (w j) 2 ((μ j).restrict
      (ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k))))
    (bound : ℕ → ℝ)
    (hbound : ∀ k, ∀ᶠ j in atTop,
      (∫ x in ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k),
        w j x ^ 2 ∂μ j) ≤ bound k) :
    ∀ k, MemLp f 2 (ν.restrict (dyadicAnnulus (e 0) R k)) ∧
      (∫ x in dyadicAnnulus (e 0) R k, f x ^ 2 ∂ν) ≤ bound k := by
  intro k
  let H := M * 2 ^ k
  have hsub := dyadic_annulus_subset_bounded_box e π K Q hπ hleft R M hM k
  have hνle : ν.restrict (dyadicAnnulus (e 0) R k) ≤
      ν.restrict (boundedProjectionRegion π (e 0) K H) := Measure.restrict_mono hsub le_rfl
  refine ⟨MemLp.mono_measure hνle (hf H), ?_⟩
  have hlocalBound : ∀ᶠ j in atTop,
      (∫ x, w j x ^ 2 ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ bound k := by
    filter_upwards [hbound k] with j hj
    have hm := Measure.restrict_mono (dyadic_bounded_box_subset_ball π (e 0) K M k)
      (le_rfl : μ j ≤ μ j)
    exact (integral_mono_measure hm (Eventually.of_forall fun x => sq_nonneg (w j x))
      (hw k j).integrable_sq).trans hj
  have hlimitBound := le_of_tendsto (hlimit H) hlocalBound
  exact (integral_mono_measure hνle (Eventually.of_forall fun x => sq_nonneg (f x))
    (hf H).integrable_sq).trans hlimitBound

end

end RieszRectifiability

end OAI
