import OAI.Geometry.RuledCovering.OuterApproximation
import OAI.Geometry.RuledCovering.Lattice

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A quantitative derivative remainder in convex local coordinates. -/
theorem c1_local_remainder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : E → F} {U : Set E} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : E} (hp : p ∈ U) {delta : ℝ} (hd : 0 < delta) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      ‖v x - v y - fderiv ℝ v p (x - y)‖ ≤ delta * ‖x - y‖ := by
  have hdc : ContinuousAt (fderiv ℝ v) p :=
    (hv.contDiffAt (hU.mem_nhds hp)).continuousAt_fderiv (by norm_num)
  have hevent : ∀ᶠ x in 𝓝 p, ‖fderiv ℝ v x - fderiv ℝ v p‖ < delta := by
    simpa only [dist_eq_norm] using hdc.eventually (ball_mem_nhds _ hd)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hevent (hU.mem_nhds hp))
  have hsub : ball p r ⊆ U := fun x hx => (hrsub hx).2
  refine ⟨r, hr, hsub, ?_⟩
  intro x hx y hy
  apply (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le' (φ := fderiv ℝ v p)
    (fun z hz => ((hv.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => (hrsub hz).1.le) hy hx

/-- Extending a nonnegative continuous weight from a compact patch does not alter it there. -/
theorem continuous_nonneg_extension {E : Type*} [TopologicalSpace E] [NormalSpace E]
    {K : Set E} (hK : IsClosed K) {f : E → ℝ} (hf : ContinuousOn f K)
    (hn : ∀ x ∈ K, 0 ≤ f x) :
    ∃ F : E → ℝ, Continuous F ∧ (∀ x, 0 ≤ F x) ∧ Set.EqOn F f K := by
  let fc : C(K, ℝ) := ⟨_, continuousOn_iff_continuous_domRestrict.mp hf⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK fc
  refine ⟨fun x => max (g x) 0, g.continuous.max continuous_const, fun x => le_max_right _ _, ?_⟩
  intro x hx
  have hgx : g x = f x := congrArg (fun q : C(K, ℝ) => q ⟨x, hx⟩) hg
  dsimp only
  rw [hgx, max_eq_left (hn x hx)]


abbrev Parameter := Fin 2 → ℝ

/-- Exact affine lattice template. The uniform bound retains finitely many centers. -/
def LatticeModel (A : Parameter →L[ℝ] Parameter) (L R : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ p : Parameter, ∀ r : ℝ, |r| ≤ L →
    ∃ b ∈ coordinateGrid n, dist b p ≤ R / n ∧
      ‖p - b + r • A (p - b)‖ ≤ 1 / (2 * n)

/-- The nonlinear local producer. Unlike tilting a continuum of lines, it produces a
finite set of intercept centers covering every label and every time simultaneously. -/
theorem local_finite_certificate {K U : Set Parameter} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (v : Parameter → Parameter)
    (A : Parameter →L[ℝ] Parameter) {L R delta : ℝ}
    (hL : 0 ≤ L) (hdelta : 0 ≤ delta) (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖v p - v b - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Parameter → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : Set Parameter, S.Finite ∧ S ⊆ U ∧
      (∀ p ∈ K, ∀ r : ℝ, |r| ≤ L → ∃ b ∈ S,
        ‖p + r • v p - (b + r • v b)‖ ≤ (1 / 2 + L * delta * R) / n) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by
  obtain ⟨n, hn, S, hSfinite, hSU, hretain, hcost⟩ :=
    (finite_weighted_grid_outer hK hU hKU hF hFpos R heps).exists
  refine ⟨n, hn, S, hSfinite, fun b hb => (hSU hb).1, ?_, hcost⟩
  intro p hp r hr
  obtain ⟨b, hbgrid, hbp, hlin⟩ := hmodel n hn p r hr
  have hbS := hretain b hbgrid ⟨p, hp, hbp⟩
  have hbp' : ‖p - b‖ ≤ R / n := by simpa [dist_eq_norm, norm_sub_rev] using hbp
  have herr := hrem p (hKU hp) b (hSU hbS).1
  refine ⟨b, hbS, ?_⟩
  calc
    ‖p + r • v p - (b + r • v b)‖ =
        ‖(p - b + r • A (p - b)) + r • (v p - v b - A (p - b))‖ := by
          congr 1
          module
    _ ≤ ‖p - b + r • A (p - b)‖ + ‖r • (v p - v b - A (p - b))‖ := norm_add_le _ _
    _ ≤ 1 / (2 * n) + L * (delta * (R / n)) := by
      apply add_le_add hlin
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (herr.trans (mul_le_mul_of_nonneg_left hbp' hdelta)) hL)
    _ = (1 / 2 + L * delta * R) / n := by ring

end RuledApproximation

end

end OAI
