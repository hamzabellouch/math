import OAI.Probability.PosteriorReplicas.Geometry.LabelEllipsoids

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma affine_infDist_orthogonal {d : ℕ} (p x : Vec d) (U : Submodule ℝ (Vec d)) :
    Metric.infDist x (AffineSubspace.mk' p U : Set (Vec d)) = ‖Uᗮ.starProjection (x-p)‖ := by
  rw [PosteriorRegression.infDist_affine_mk', Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

def tupleDistance {d m : ℕ} (u : Tuple d m) (x : Vec d) : ℝ :=
  ‖(differenceSpan u)ᗮ.starProjection (x-u 0)‖

lemma tupleDistance_eq_infDist {d m : ℕ} (u : Tuple d m) (x : Vec d) :
    tupleDistance u x = Metric.infDist x (AffineSubspace.mk' (u 0) (differenceSpan u) : Set (Vec d)) :=
  (affine_infDist_orthogonal _ _ _).symm

@[fun_prop] lemma measurable_tupleDistance_fixed {d m : ℕ} (u : Tuple d m) :
    Measurable (tupleDistance u) := by unfold tupleDistance; fun_prop

lemma differenceSpan_finrank_le {d m : ℕ} (u : Tuple d m) :
    Module.finrank ℝ (differenceSpan u) ≤ m := by
  change Module.finrank ℝ (Submodule.span ℝ (range (differences u))) ≤ m
  simpa only [Set.finrank, Fintype.card_fin] using
    finrank_range_le_card (R := ℝ) (differences u)

lemma tupleDistance_tube {d k m : ℕ} (hd : k+m+2 ≤ d) (u : Tuple d m)
    {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞} (hfL : ∀ x, f x ≤ L)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (sphereLaw d).withDensity f {x | tupleDistance u x ≤ r} ≤
      (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal (r^(k+1)) := by
  let : NeZero d := ⟨by omega⟩
  simp_rw [tupleDistance_eq_infDist]
  apply spherical_tilt_affine_tube hfL _ _ hr hr1
  rw [AffineSubspace.direction_mk']
  have h := differenceSpan_finrank_le u
  omega

lemma tupleDistance_pos_ae {d m : ℕ} (hd : 3 ≤ d) (hm : m < d) (u : Tuple d m)
    (f : Vec d → ℝ≥0∞) :
    ∀ᵐ x ∂(sphereLaw d).withDensity f, 0 < tupleDistance u x := by
  let S := AffineSubspace.mk' (u 0) (differenceSpan u)
  have hz : sphereLaw d S = 0 := by
    apply base_affine_null hd .spherical S
    rw [AffineSubspace.direction_mk']
    exact (differenceSpan_finrank_le u).trans_lt hm
  have hn : ∀ᵐ x ∂sphereLaw d, x ∉ S := by
    rw [ae_iff]
    simp only [not_not]
    convert hz using 2
    ext x
    rfl
  filter_upwards [(withDensity_absolutelyContinuous (sphereLaw d) f).ae_le hn] with x hx
  rw [tupleDistance_eq_infDist]
  exact (S.closed_of_finiteDimensional.notMem_iff_infDist_pos
    ⟨u 0, AffineSubspace.self_mem_mk' _ _⟩).mp hx

lemma labels_sub {d k : ℕ} (A : Rows d k) (x y : Vec d) :
    labels A (x-y) = labels A x - labels A y := by
  ext i
  simp [labels, inner_sub_right]

lemma constrained_label_lift_le {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (U : Submodule ℝ (Vec d)) (hU : ∀ i, A i ∈ Uᗮ) (p x : Vec d) :
    ‖liftLabel A (labels A x - labels A p)‖ ≤ ‖Uᗮ.starProjection (x-p)‖ := by
  have he : labels A (Uᗮ.starProjection (x-p)) = labels A (x-p) := by
    ext i
    change ⟪A i,Uᗮ.starProjection (x-p)⟫ = ⟪A i,x-p⟫
    rw [← Uᗮ.inner_starProjection_left_eq_right,
      Uᗮ.starProjection_eq_self_iff.mpr (hU i)]
  rw [← labels_sub, ← he, liftLabel_eq_pairingLift]
  change ‖pairingLift A (fun i => ⟪A i,Uᗮ.starProjection (x-p)⟫)‖ ≤ _
  rw [← starProjection_eq_pairingLift hA]
  exact Submodule.norm_starProjection_apply_le _ _

lemma constrained_tube_le_ellipsoid {d k m : ℕ} (ν : Measure (Vec d))
    (u : Tuple d m) {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hU : ∀ i, A i ∈ (differenceSpan u)ᗮ) (r : ℝ) :
    ν {x | tupleDistance u x ≤ r} ≤
      ν {x | ‖liftLabel A (labels A x - labels A (u 0))‖ ≤ r} := by
  apply measure_mono
  intro x hx
  exact (constrained_label_lift_le hA _ hU _ _).trans hx

lemma density_inverse_moment_bins {d k m : ℕ} (hd : k+m+2 ≤ d)
    (u : Tuple d m) {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞} (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1)
    {A : Rows d k} (hA : LinearIndependent ℝ A) (hU : ∀ i, A i ∈ (differenceSpan u)ᗮ) :
    (∫⁻ x, ENNReal.ofReal ((tupleDistance u x)⁻¹^k) ∂(sphereLaw d).withDensity f) ≤
      2 + ∑ j ∈ Finset.range J, ENNReal.ofReal ((2:ℝ)^(k*(j+1))) *
        (sphereLaw d).withDensity f {x | ‖liftLabel A (labels A x-labels A (u 0))‖ ≤ (1/2:ℝ)^j} := by
  apply (inverse_moment_finite_bins _ (measurable_tupleDistance_fixed u)
    (fun x => norm_nonneg _) k J _ (fun r hr hr1 => tupleDistance_tube hd u hfL hr hr1) hcut).trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul' le_rfl (constrained_tube_le_ellipsoid _ u hA hU _)

end PosteriorReplicas
end

end OAI
