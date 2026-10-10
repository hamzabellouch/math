import OAI.Geometry.RCD.Sobolev.LocalGradientRepresentative

namespace OAI

/-! # Local amplitude bounds from the actual weak gradient

Local transport and differentiation supply Lipschitz representatives. A
finite cover then bounds the original Sobolev function on each compact
interior ball, without assuming an amplitude bound.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.local_sobolev_lipschitz
    {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic)
    (L : ℝ≥0) {p : X} {R : ℝ} (hR : 0 < R)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * R)),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2) :
    ∃ v : X → ℝ, LipschitzWith L v ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic f
        =ᵐ[(hausdorff n X).restrict (closedBall p R)] v := by
  let μ := hausdorff n X
  apply hX.local_lipschitz_representative hn
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic f) L hR
  filter_upwards [hL, ae_restrict_of_ae (localGamma_self μ hX.quadratic f),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr
      (SobolevSpace.minimalSlope_nonneg μ hX.quadratic f))] with x hx he hg
  rw [he] at hx
  change 0 ≤ SobolevSpace.minimalSlope μ hX.quadratic f x at hg
  exact (sq_le_sq₀ hg L.coe_nonneg).mp hx

theorem NoncollapsedRCD.local_amplitude_of_gradient
    {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ≥0)
    {p : X} {a b : ℝ} (hab : a < b)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2) :
    ∃ A : ℝ≥0, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p a),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A := by
  classical
  let μ := hausdorff n X
  let δ := (b - a) / 16
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlocal (q : closedBall p a) :
      ∃ v : X → ℝ, LipschitzWith L v ∧
        SobolevSpace.toLp μ hX.quadratic f =ᵐ[μ.restrict (closedBall (q : X) δ)] v := by
    apply hX.local_sobolev_lipschitz hn f L hδ
    apply ae_restrict_of_ae_restrict_of_subset _ hL
    intro x hx
    have hq : dist (q : X) p ≤ a := q.property
    have hxq : dist x (q : X) < 8 * δ := hx
    change dist x p < b
    have ht := dist_triangle x (q : X) p
    dsimp only [δ] at hxq
    linarith
  choose v hv he using hlocal
  obtain ⟨s, hs⟩ := (isCompact_closedBall p a).elim_finite_subcover
    (fun q : closedBall p a => ball (q : X) δ) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using hδ⟩)
  let M (q : closedBall p a) : ℝ := |v q q| + L * δ
  have hM (q : closedBall p a) : 0 ≤ M q := add_nonneg (abs_nonneg _) (mul_nonneg L.coe_nonneg hδ.le)
  let A : ℝ≥0 := ⟨∑ q ∈ s, M q, Finset.sum_nonneg fun q _ => hM q⟩
  refine ⟨A, ?_⟩
  have hbound (q : closedBall p a) : ∀ᵐ x ∂μ,
      x ∈ ball (q : X) δ → |SobolevSpace.toLp μ hX.quadratic f x| ≤ M q := by
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp (he q)] with x hx hball
    rw [hx (ball_subset_closedBall hball)]
    have hd := (hv q).dist_le_mul x q
    have hxδ : dist x (q : X) < δ := hball
    have ht := abs_add_le (v q x - v q q) (v q q)
    rw [sub_add_cancel] at ht
    dsimp only [M]
    rw [Real.dist_eq] at hd
    nlinarith [mul_le_mul_of_nonneg_left hxδ.le L.coe_nonneg]
  have hall := (Filter.eventually_all_finset s).mpr (fun q _ => hbound q)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_closedBall] with x hx hxball
  obtain ⟨q, hqs, hxq⟩ := mem_iUnion₂.mp (hs hxball)
  exact (hx q hqs hxq).trans (Finset.single_le_sum (fun q _ => hM q) hqs)

end RegularPointCoordinates

end

end OAI
