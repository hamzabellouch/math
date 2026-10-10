import OAI.Geometry.SurfaceImmersion.Geometry.PureRayAvoidance

namespace OAI

/-! Uniform nonvanishing and avoidance of the negative preferred normal on
compact curve pieces.  The collar case has an independent positive invariant. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.GeometryPreservation

lemma pure_first_positive_of_collar {S D N L k b c : ℝ} (hS : 0 < S)
    (hcollar : 0 < (D*b+S*c)^2+k*b^2) :
    0 < (pureComponents S D N L k b c).1 := by
  have hid := pure_first_identity (D := D) (N := N) (L := L) (k := k)
    (b := b) (c := c) hS.ne'
  nlinarith [mul_nonneg (sq_nonneg N) (sq_nonneg b)]

theorem compact_curve_avoidance {X : Type*} [TopologicalSpace X]
    (sLo K d : ℝ) (hmin : 0 < sLo) (hK : 0 ≤ K) (hd : 0 ≤ d) :
    ∃ H : ℝ, 0 < H ∧ ∀ C : Set X, IsCompact C →
    ∀ A N₀ : X → ℝ, Continuous A → Continuous N₀ →
    (∀ x ∈ C, A x = 0 → H+2 < |N₀ x|) →
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ C,
    ∀ S D N L k b c : ℝ, sLo ≤ S → -K ≤ k → |D| ≤ d →
      (b ≠ 0 ∨ c ≠ 0) → |N-N₀ x| < η → |z*L-A x| < η →
      0 < (pureComponents S D N L k b c).1 ∨
        (pureComponents S D N L k b c).2 ≠ 0 := by
  let H := K+2
  refine ⟨H,by dsimp [H]; positivity,?_⟩
  intro C hC A N₀ hA hN₀ hturn
  obtain ⟨B,hB⟩ := (hC.image hN₀.abs).bddAbove
  let B₀ := max 0 B+1
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have hbound : ∀ x ∈ C, |N₀ x| ≤ max 0 B := fun x hx =>
    (hB (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  let J := 2*B₀*((Real.sqrt K+d)/sLo)+1
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨η₀,hη₀,halt⟩ := small_scale_turn_or_longitudinal hC hA hN₀ H J hJ.le hturn
  refine ⟨min 1 η₀,lt_min (by norm_num) hη₀,?_⟩
  intro z hz hzη x hx S D N L k b c hS hk hD hv hN hL
  have hNsmall : |N-N₀ x| < 1 := hN.trans_le (min_le_left _ _)
  have hNbound : |N| ≤ B₀ := by
    have hh := abs_sub_le N (N₀ x) 0
    simp only [sub_zero] at hh
    dsimp [B₀]
    linarith [hbound x hx]
  apply pure_ray_avoidance_of_slopes (hmin.trans_le hS) hv
  intro t
  rcases halt z hz (hzη.trans_le (min_le_right _ _)) x hx N L hNsmall
      (hL.trans_le (min_le_right _ _)) with hlargeN | hlargeL
  · apply Or.inl
    apply slope_first_positive (hmin.trans_le hS) hk
    dsimp [H] at hlargeN
    nlinarith [sq_abs N,abs_nonneg N]
  · exact slope_ray_avoidance_longitudinal hmin hS hK hk hD hB₀ hNbound
      (by dsimp [J] at hlargeL; linarith)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
