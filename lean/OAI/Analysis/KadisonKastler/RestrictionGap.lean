import OAI.Analysis.KadisonKastler.QuotientUnitBall
import OAI.Analysis.KadisonKastler.ReducingRestriction
import OAI.Analysis.KadisonKastler.SeparableAlgebraPair

namespace OAI

/-! # The ordinary gap decreases under a common reducing restriction

Exact contraction lifts through the two restriction homomorphisms avoid
any faithfulness assumption and lose no radius in the gap estimate.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (K : Submodule ℂ H) [CompleteSpace K]
  (A B : StarSubalgebra ℂ (H →L[ℂ] H))
  (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
  (hB : ∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K)

theorem starAlgebraBall_hausdorffEDist_ne_top :
    Metric.hausdorffEDist (starAlgebraBall A) (starAlgebraBall B) ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    ⟨0, zero_mem_starAlgebraBall A⟩ ⟨0, zero_mem_starAlgebraBall B⟩
    (isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hx => hx.2⟩)
    (isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hx => hx.2⟩)

theorem exists_restriction_ball_approx
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H)))
    {r : ℝ} (hr : Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < r)
    {x : K →L[ℂ] K} (hx : x ∈ starAlgebraBall (reducingRestriction K A hA).range) :
    ∃ y ∈ starAlgebraBall (reducingRestriction K B hB).range, ‖x - y‖ < r := by
  let : CStarAlgebra A := StarSubalgebra.cstarAlgebra A (h_closed := hAc)
  let : CStarAlgebra B := StarSubalgebra.cstarAlgebra B (h_closed := hBc)
  obtain ⟨a, ha, haeq⟩ := exists_contractive_starAlgHom_preimage
    (reducingRestriction K A hA) hx.1 hx.2
  obtain ⟨b, hb, hab⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
    (show a.val ∈ starAlgebraBall A from ⟨a.property, ha⟩) hr
    (starAlgebraBall_hausdorffEDist_ne_top A B)
  let b' : B := ⟨b, hb.1⟩
  refine ⟨reducingRestriction K B hB b',
    ⟨⟨b', rfl⟩, (NonUnitalStarAlgHom.norm_apply_le _ b').trans hb.2⟩, ?_⟩
  have hnorm : ‖x - reducingRestriction K B hB b'‖ ≤ ‖a.val - b‖ := by
    rw [← haeq]
    change ‖cornerCompression K a.val - cornerCompression K b‖ ≤ ‖a.val - b‖
    rw [← map_sub]
    exact norm_cornerCompression_le K _
  exact hnorm.trans_lt (by simpa only [dist_eq_norm] using hab)

/-- Restriction can have a kernel on either algebra. It still decreases
the distance of their closed unit balls. -/
theorem restriction_gap_le
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H))) :
    Metric.hausdorffDist (starAlgebraBall (reducingRestriction K A hA).range)
      (starAlgebraBall (reducingRestriction K B hB).range) ≤
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  apply Metric.hausdorffDist_le_of_mem_dist (Metric.hausdorffDist_nonneg.trans hr.le)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_restriction_ball_approx K A B hA hB hAc hBc hr hx
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy.le⟩
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := exists_restriction_ball_approx K B A hB hA hBc hAc
      (by simpa only [Metric.hausdorffDist_comm] using hr) hy
    exact ⟨x, hx, by simpa only [dist_eq_norm] using hyx.le⟩

end

end KadisonKastler

end OAI
