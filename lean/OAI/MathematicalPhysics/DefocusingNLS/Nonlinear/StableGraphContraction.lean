import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphForward
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! # A Banach contraction for the forward/backward recurrence

All inputs are explicit estimates on the two linear blocks and the two
nonlinear remainder maps.  This is the recurrence lemma used by `nl:graph`,
not an assumption of the spectral splitting or the stable graph itself.
The mixed block is small after weighting the finite-dimensional coordinates.
-/

open Set Metric

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def stableGraphMap (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (hA : ∀ n, ‖A n‖ ≤ 1 / 8) (hB : ∀ n, ‖B n‖ ≤ 1 / 16)
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1) (w₀ : E)
    (N : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ E))
    (H : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ F))
    (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) : (ℕ →ᵇ E) × (ℕ →ᵇ F) :=
  (stableForward A B (1 / 8) (1 / 16) (by norm_num) (by norm_num) hA hB
    w₀ x.1 x.2 (N x), stableBackward R hR (H x))

omit [CompleteSpace E] in
theorem stableGraphMap_dist_le (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (hA : ∀ n, ‖A n‖ ≤ 1 / 8) (hB : ∀ n, ‖B n‖ ≤ 1 / 16)
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1) (w₀ : E)
    (N : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ E))
    (H : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ F))
    (x y : (ℕ →ᵇ E) × (ℕ →ᵇ F))
    (hN : dist (N x) (N y) ≤ (1 / 16 : ℝ) * dist x y)
    (hH : dist (H x) (H y) ≤ (1 / 16 : ℝ) * dist x y) :
    dist (stableGraphMap A B hA hB R hR w₀ N H x)
      (stableGraphMap A B hA hB R hR w₀ N H y) ≤ (1 / 2 : ℝ) * dist x y := by
  have hfst : dist x.1 y.1 ≤ dist x y := le_max_left _ _
  have hsnd : dist x.2 y.2 ≤ dist x y := le_max_right _ _
  change max (dist _ _) (dist _ _) ≤ _
  apply max_le
  · apply (stableForward_dist_le A B (1 / 8) (1 / 16) (by norm_num) (by norm_num)
      hA hB w₀ x.1 y.1 x.2 y.2 (N x) (N y)).trans
    linarith
  · apply (stableBackward_dist_le R hR (H x) (H y)).trans
    nlinarith [show 0 ≤ dist x y from dist_nonneg]

omit [CompleteSpace E] in
theorem stableGraphMap_zero_bound (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (hA : ∀ n, ‖A n‖ ≤ 1 / 8) (hB : ∀ n, ‖B n‖ ≤ 1 / 16)
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1) (w₀ : E)
    (N : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ E))
    (H : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ F))
    (ε : ℝ) (hε : 0 ≤ ε) (hN : ‖N 0‖ ≤ ε) (hH : ‖H 0‖ ≤ ε) :
    ‖stableGraphMap A B hA hB R hR w₀ N H 0‖ ≤ ‖w₀‖ + 2 * ε := by
  change max ‖stableForward A B (1 / 8) (1 / 16) (by norm_num) (by norm_num)
      hA hB w₀ 0 0 (N 0)‖
    ‖stableBackward R hR (H 0)‖ ≤ _
  apply max_le
  · apply (stableForward_norm_le A B (1 / 8) (1 / 16) (by norm_num) (by norm_num)
      hA hB w₀ 0 0 (N 0)).trans
    simp only [norm_zero, mul_zero, zero_add]
    apply max_le <;> nlinarith [norm_nonneg w₀]
  · exact (norm_stableBackward_le R hR (H 0)).trans (by nlinarith [norm_nonneg w₀])

theorem exists_stableGraph_fixedPoint
    (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (hA : ∀ n, ‖A n‖ ≤ 1 / 8) (hB : ∀ n, ‖B n‖ ≤ 1 / 16)
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1) (w₀ : E)
    (N : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ E))
    (H : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ F))
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hN : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (N x) (N y) ≤ (1 / 16 : ℝ) * dist x y)
    (hH : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (H x) (H y) ≤ (1 / 16 : ℝ) * dist x y)
    (hN0 : ‖N 0‖ ≤ ε) (hH0 : ‖H 0‖ ≤ ε)
    (hsmall : ‖w₀‖ + 2 * ε ≤ ρ / 2) :
    ∃ x : (ℕ →ᵇ E) × (ℕ →ᵇ F), ‖x‖ ≤ ρ ∧
      stableGraphMap A B hA hB R hR w₀ N H x = x ∧
      ‖x‖ ≤ 2 * (‖w₀‖ + 2 * ε) ∧
      (∀ y, ‖y‖ ≤ ρ → stableGraphMap A B hA hB R hR w₀ N H y = y → y = x) := by
  let P := stableGraphMap A B hA hB R hR w₀ N H
  have hzero : (0 : (ℕ →ᵇ E) × (ℕ →ᵇ F)) ∈ closedBall 0 ρ := by
    simpa only [mem_closedBall, dist_self] using hρ
  have hp0 : ‖P 0‖ ≤ ‖w₀‖ + 2 * ε := stableGraphMap_zero_bound A B hA hB R hR w₀
    N H ε hε hN0 hH0
  have hlip (x y : (ℕ →ᵇ E) × (ℕ →ᵇ F))
      (hx : x ∈ closedBall 0 ρ) (hy : y ∈ closedBall 0 ρ) :
      dist (P x) (P y) ≤ (1 / 2 : ℝ) * dist x y := by
    have hx' : ‖x‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hy' : ‖y‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hy
    exact stableGraphMap_dist_le A B hA hB R hR w₀ N H x y
      (hN x y hx' hy') (hH x y hx' hy')
  have hmap : MapsTo P (closedBall 0 ρ) (closedBall 0 ρ) := by
    intro x hx
    have hx' : ‖x‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hh := hlip x 0 hx hzero
    have ht := dist_triangle (P x) (P 0) 0
    simp only [mem_closedBall, dist_zero_right] at hh ht ⊢
    linarith
  have hcontract : ContractingWith (1 / 2)
      (hmap.restrict P (closedBall 0 ρ) (closedBall 0 ρ)) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact hlip x.1 y.1 x.2 y.2
  obtain ⟨x, hx, hfix, _⟩ := hcontract.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hzero (edist_ne_top _ _)
  have hxnorm : ‖x‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hbound : ‖x‖ ≤ 2 * (‖w₀‖ + 2 * ε) := by
    have hh := hlip x 0 hx hzero
    have ht := dist_triangle (P x) (P 0) 0
    rw [hfix] at hh ht
    simp only [dist_zero_right] at hh ht
    linarith
  refine ⟨x, hxnorm, hfix, hbound, ?_⟩
  intro y hy hyfix
  change P y = y at hyfix
  have hyball : y ∈ closedBall 0 ρ := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hh := hlip y x hyball hx
  rw [hyfix, hfix] at hh
  exact dist_eq_zero.mp (by linarith [show 0 ≤ dist y x from dist_nonneg])

end DefocusingNLS

end OAI
