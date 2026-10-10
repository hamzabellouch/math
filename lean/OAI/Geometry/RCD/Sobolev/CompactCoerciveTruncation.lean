import OAI.Geometry.RCD.Sobolev.CompactLipschitzLocalization

namespace OAI

/-! # Compact Lipschitz truncation preserving a prescribed working ball -/

open Set Metric
open scoped NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem compact_coercive_truncation (p : X) (Φ : X → ℝ)
    (hlip : ∀ r : ℝ, 0 < r → ∃ L : ℝ≥0, LipschitzOnWith L Φ (closedBall p r))
    (hcoerce : ∀ M : ℝ, ∃ r : ℝ, 0 ≤ r ∧ ∀ x, r ≤ dist p x → M ≤ Φ x)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ (M r : ℝ) (L : ℝ≥0), 0 ≤ r ∧
      LipschitzWith L (fun x => min (Φ x) M - M) ∧
      HasCompactSupport (fun x => min (Φ x) M - M) ∧
      (∀ x, r < dist p x → min (Φ x) M - M = 0) ∧
      ∀ x ∈ closedBall p R, min (Φ x) M - M = Φ x - M := by
  obtain ⟨L₀,hL₀⟩ := hlip (R+1) (by linarith)
  let M := Φ p + (L₀ : ℝ) * (R+1) + 1
  obtain ⟨r,hr,hout⟩ := hcoerce M
  obtain ⟨L₁,hL₁⟩ := hlip (r+1) (by linarith)
  let f : X → ℝ := fun x => min (Φ x) M - M
  have hfl : LipschitzOnWith L₁ f (closedBall p (r+1)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hm := (LipschitzWith.id.min_const M).dist_le_mul (Φ x) (Φ y)
    have he : dist (f x) (f y) = dist (min (Φ x) M) (min (Φ y) M) := by
      simp only [f, Real.dist_eq]
      congr 1
      ring
    rw [he]
    have hm' : dist (min (Φ x) M) (min (Φ y) M) ≤ dist (Φ x) (Φ y) := by
      simpa only [id_eq,NNReal.coe_one,one_mul] using hm
    exact hm'.trans (hL₁.dist_le_mul x hx y hy)
  have hf0 (x : X) (hx : r < dist p x) : f x = 0 := by
    dsimp [f]
    rw [min_eq_right (hout x hx.le),sub_self]
  obtain ⟨L,hL⟩ := lipschitz_of_ball_and_zero p hr hfl hf0
  refine ⟨M,r,L,hr,hL,?_,hf0,?_⟩
  · apply HasCompactSupport.intro (isCompact_closedBall p r)
    intro x hx
    apply hf0 x
    simpa only [mem_closedBall,dist_comm,not_le] using hx
  · intro x hx
    have hx' : x ∈ closedBall p (R+1) := by
      exact closedBall_subset_closedBall (by linarith) hx
    have hp : p ∈ closedBall p (R+1) := mem_closedBall_self (by linarith)
    have hdist : dist x p ≤ R := hx
    have hh := hL₀.le_add_mul hx' hp
    have hm : Φ x ≤ M := by
      dsimp [M]
      nlinarith [mul_le_mul_of_nonneg_left hdist L₀.coe_nonneg]
    rw [min_eq_left hm]

end RegularPointCoordinates

end OAI
