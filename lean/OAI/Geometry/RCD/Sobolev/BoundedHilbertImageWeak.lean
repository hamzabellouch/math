import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Weak convergence from a bounded injective Hilbert-space image

The adjoint range is dense. A uniform bound extends convergence from
these image pairings to every Hilbert test vector.
-/

open Set Filter Metric
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem adjoint_denseRange_of_injective (T : E →L[ℝ] F) (hT : Function.Injective T) :
    DenseRange T.adjoint := by
  change Dense (T.adjoint.range : Set E)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hker : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hT
  rw [← T.orthogonal_ker,hker,Submodule.bot_orthogonal_eq_top]

theorem bounded_hilbert_image_inner_tendsto
    (T : E →L[ℝ] F) (hT : Function.Injective T)
    (u : ℕ → E) (v : E) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖u k‖ ≤ C)
    (hc : Tendsto (fun k => T (u k)) atTop (𝓝 (T v))) (z : E) :
    Tendsto (fun k => inner ℝ z (u k)) atTop (𝓝 (inner ℝ z v)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := C+‖v‖+1
  have hA : 0 < A := by dsimp only [A]; positivity
  obtain ⟨y,hy⟩ := Metric.denseRange_iff.mp (adjoint_denseRange_of_injective T hT)
    z (ε/(2*A)) (by positivity)
  have hy' : ‖z-T.adjoint y‖ < ε/(2*A) := by simpa only [dist_eq_norm] using hy
  have hm := (tendsto_const_nhds (x := y)).inner (𝕜 := ℝ) (hc.sub_const (T v))
  simp only [sub_self,inner_zero_right] at hm
  have hmnorm := hm.norm
  simp only [norm_zero] at hmnorm
  have hs : ∀ᶠ k in atTop, ‖inner ℝ y (T (u k)-T v)‖ < ε/2 :=
    hmnorm.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hs] with k hk
  have hdiff : ‖u k-v‖ ≤ A :=
    (norm_sub_le _ _).trans (by dsimp only [A]; linarith [hb k])
  have herr : |inner ℝ (z-T.adjoint y) (u k-v)| < ε/2 := by
    calc
      _ ≤ ‖z-T.adjoint y‖*‖u k-v‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (z-T.adjoint y) (u k-v)
      _ ≤ ‖z-T.adjoint y‖*A := mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
      _ < (ε/(2*A))*A := mul_lt_mul_of_pos_right hy' hA
      _ = ε/2 := by field_simp
  have he : inner ℝ z (u k)-inner ℝ z v =
      inner ℝ (z-T.adjoint y) (u k-v) + inner ℝ y (T (u k)-T v) := by
    rw [← map_sub,← T.adjoint_inner_left,inner_sub_left,inner_sub_right]
    ring
  rw [Real.dist_eq,he]
  have hk' : |inner ℝ y (T (u k)-T v)| < ε/2 := by simpa only [Real.norm_eq_abs] using hk
  exact (abs_add_le _ _).trans_lt (by linarith)

end RegularPointCoordinates

end

end OAI
