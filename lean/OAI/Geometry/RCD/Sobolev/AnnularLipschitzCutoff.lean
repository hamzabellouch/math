import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests

namespace OAI

/-! # Compact Lipschitz cutoffs with any positive annular width -/

open Set Metric
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_annular_lipschitz_cutoff (p : X) {a b : ℝ} (hab : a < b) :
    ∃ (χ : X →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L χ ∧
      HasCompactSupport (χ : X → ℝ) ∧ tsupport χ ⊆ closedBall p b ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ closedBall p a, χ x = 1) := by
  let f (x : X) := clipUnit ((b - dist p x) / (b - a))
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hb (x : X) : 0 ≤ f x ∧ f x ≤ 1 := clipUnit_bounds _
  have hl : LipschitzWith ⟨(b - a)⁻¹, inv_nonneg.mpr hgap.le⟩ f := by
    have h := clipUnit_lipschitz.comp
      ((lipschitzWith_const_mul_real (LipschitzWith.dist_right p) (-((b - a)⁻¹))).add
        (LipschitzWith.const (b / (b - a))))
    have hc : (1 : ℝ≥0) * (‖-((b - a)⁻¹)‖₊ * 1 + 0) =
        ⟨(b - a)⁻¹, inv_nonneg.mpr hgap.le⟩ := by
      ext
      simp only [coe_nnnorm, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (inv_nonneg.mpr hgap.le), mul_one, one_mul, add_zero]
      rfl
    rw [hc] at h
    convert h using 1
    funext x
    dsimp only [Function.comp_apply, f]
    congr 1
    ring
  have hs : tsupport f ⊆ closedBall p b := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    have hd : b < dist p x := by simpa only [mem_closedBall, dist_comm, not_le] using hn
    apply hx
    dsimp [f, clipUnit]
    rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith) hgap.le),
      min_eq_left zero_le_one]
  let χ : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f hl.continuous 1
    (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2)
  refine ⟨χ, _, hl, (isCompact_closedBall p b).of_isClosed_subset (isClosed_tsupport _) hs,
    hs, hb, ?_⟩
  intro x hx
  have hd : dist p x ≤ a := by simpa only [mem_closedBall, dist_comm] using hx
  have hrat : 1 ≤ (b - dist p x) / (b - a) := (le_div_iff₀ hgap).mpr (by linarith)
  change clipUnit ((b - dist p x) / (b - a)) = 1
  rw [clipUnit, max_eq_left (zero_le_one.trans hrat), min_eq_right hrat]

end RegularPointCoordinates

end

end OAI
