import OAI.Analysis.KadisonKastler.NearInclusionDistance

namespace OAI

/-! # Composition of approximate normalizers with unit-ball normalization -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem infDist_unitaryConj_mul_le (M : VonNeumannAlgebra H)
    (u v : unitary (H →L[ℂ] H)) {e f : ℝ}
    (hu : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) u x)
      (M : Set (H →L[ℂ] H)) ≤ e)
    (hv : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) v x)
      (M : Set (H →L[ℂ] H)) ≤ f) (x : H →L[ℂ] H) (hx : x ∈ unitBall M) :
    Metric.infDist (unitaryConj (H := H) (u * v) x) (M : Set (H →L[ℂ] H)) ≤ e + 2 * f := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hnear : Metric.infDist (unitaryConj (H := H) v x) (M : Set (H →L[ℂ] H)) <
      (r - e) / 2 := (hv x hx).trans_lt (by linarith)
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff
    (show (M : Set (H →L[ℂ] H)).Nonempty from ⟨0, M.zero_mem⟩)).mp hnear
  obtain ⟨z, hz, hxz⟩ := exists_unitBall_approx_of_algebra_approx
    (N := M) (x := unitaryConj (H := H) v x) (y := y) (by simpa only [norm_unitaryConj] using hx.2) hy
  have hbound : ‖unitaryConj (H := H) v x - z‖ < r - e := by
    rw [dist_eq_norm] at hxy
    exact hxz.trans_lt (by linarith)
  have h := Metric.infDist_le_infDist_add_dist
    (x := unitaryConj (H := H) (u * v) x) (y := unitaryConj (H := H) u z)
    (s := (M : Set (H →L[ℂ] H)))
  rw [unitaryConj_mul, dist_eq_norm, ← unitaryConj_sub, norm_unitaryConj] at h
  simpa only [unitaryConj_mul] using
    (h.trans (add_le_add (hu z hz) hbound.le)).trans_eq (show e + (r - e) = r by ring)

end

end KadisonKastler

end OAI
