import OAI.Geometry.IsometricImmersion.Caps.BoundedClassCapRadius
import OAI.Geometry.IsometricImmersion.Metrics.MetricPatchOpen

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem inverseShear_slab_mem_centralBox {L r q0 : ℝ} {p : Coord}
    (hL : 1 ≤ L) (hr : 0 ≤ r) (hLr : L * r ≤ 1 / 20) (hq0 : |q0| ≤ 1 / 20)
    (hx : |p 0| ≤ L * r) (hy : |p 1| ≤ r) :
    inverseShearCoordinates q0 p ∈ centralBox := by
  have hrL : r ≤ L * r := by nlinarith
  have hrsmall : r ≤ 1 / 20 := hrL.trans hLr
  have hxsmall : |p 0| ≤ 1 / 20 := hx.trans hLr
  have hprod : |q0 * p 0| ≤ (1 / 20 : ℝ) * (1 / 20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hxsmall (abs_nonneg _) (by norm_num)
  have hysmall : |p 1 - q0 * p 0| ≤ (1 / 20 : ℝ) + (1 / 20) * (1 / 20) :=
    (abs_sub _ _).trans (add_le_add (hy.trans hrsmall) hprod)
  change (fun _ => -(1 / 5 : ℝ)) ≤ inverseShearCoordinates q0 p ∧
    inverseShearCoordinates q0 p ≤ (fun _ => (1 / 5 : ℝ))
  constructor
  · intro i
    fin_cases i
    · change -(1 / 5 : ℝ) ≤ p 0
      linarith [(abs_le.mp hxsmall).1]
    · change -(1 / 5 : ℝ) ≤ p 1 - q0 * p 0
      linarith [(abs_le.mp hysmall).1]
  · intro i
    fin_cases i
    · change p 0 ≤ (1 / 5 : ℝ)
      linarith [(abs_le.mp hxsmall).2]
    · change p 1 - q0 * p 0 ≤ (1 / 5 : ℝ)
      linarith [(abs_le.mp hysmall).2]

theorem shrinking_class_slab_axis_bounds {kappa r b : ℝ} {M : ℕ} {p : Coord}
    (hr : 0 ≤ r) (hb : b ≤ 0)
    (hp : p ∈ shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
      (-r) b (boundedClassWidth kappa M / 4)) :
    |p 0| ≤ boundedClassWidth kappa M * r ∧ |p 1| ≤ r := by
  have ht := hp.1
  have hx := hp.2
  have hspeed : 0 ≤ boundedClassWidth kappa M / 4 :=
    div_nonneg (boundedClassWidth_pos kappa M).le (by norm_num)
  have hmove : 0 ≤ (boundedClassWidth kappa M / 4) * (p 1 - (-r)) :=
    mul_nonneg hspeed (sub_nonneg.mpr ht.1)
  unfold inwardLeft inwardRight at hx
  exact ⟨abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    abs_le.mpr ⟨ht.1, by linarith [ht.2]⟩⟩

theorem actual_patch_curvature_on_class_slab {g0 : MetricField} {kappa q0 r b : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa) (hr : 0 ≤ r) (hb : b ≤ 0)
    (hLr : boundedClassWidth kappa M * r ≤ 1 / 20) (hq0 : |q0| ≤ 1 / 20)
    {p : Coord}
    (hp : p ∈ shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
      (-r) b (boundedClassWidth kappa M / 4)) :
    inverseShearCoordinates q0 p ∈ centralBox ∧
    gaussianCurvature (perturbedMetric g0 eta.val) (inverseShearCoordinates q0 p) < -kappa / 2 := by
  obtain ⟨hx, hy⟩ := shrinking_class_slab_axis_bounds hr hb hp
  have hc := inverseShear_slab_mem_centralBox
    ((by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)) hr hLr hq0 hx hy
  exact ⟨hc, eta.property.2 _ hc⟩

theorem exists_bounded_patch_actual_slab_QLowBounds
    (G kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) (hq0 : |q0| ≤ 1 / 20) :
    ∃ MQ : ℝ, 0 ≤ MQ ∧ ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa)
      (z : Coord → ℝ) (r b : ℝ),
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z → 0 ≤ r → b ≤ 0 →
      boundedClassWidth kappa M * r ≤ 1 / 20 →
      heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
        (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤
          9 / (100 * boundedClassWidth kappa M) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
      |hessianQuotient (perturbedMetric g0 eta.val) z 0 - q0| ≤
        1 / (100 * boundedClassWidth kappa M) →
      QLowBounds (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (heightInShearCoordinates z q0)
        (shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
          (-r) b (boundedClassWidth kappa M / 4))
        (shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)) MQ (boundedClassWidth kappa M / 4) := by
  obtain ⟨MQ, hMQ, hlow⟩ := exists_bounded_class_cap_radius_QLowBounds
    G 1 kappa d q0 M hG (by norm_num) hkappa hd hM hq0
  refine ⟨MQ, hMQ, ?_⟩
  intro g0 eta z r b hclass hr hb hLr hrsmall hgB hdet hcenter
  let S := shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
    (-r) b (boundedClassWidth kappa M / 4)
  have haxes (p : Coord) (hp : p ∈ S) := shrinking_class_slab_axis_bounds hr hb hp
  have hcentral (p : Coord) (hp : p ∈ S) := actual_patch_curvature_on_class_slab eta hr hb hLr hq0 hp
  have hrsmall' : r ≤ 1 / 20 := by
    have hL : 1 ≤ boundedClassWidth kappa M :=
      (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
    have hh : r ≤ boundedClassWidth kappa M * r := by nlinarith
    exact hh.trans hLr
  exact hlow (perturbedMetric g0 eta.val) z S r hclass hr hrsmall
    (fun p hp => centralBox_subset_modelSquare (hcentral p hp).1)
    (fun p hp => ⟨by linarith [(haxes p hp).1], by linarith [(haxes p hp).2]⟩)
    haxes hgB hdet (fun p hp => (hcentral p hp).2.le) hcenter

end SmoothLocal.Perturbation

end

end OAI
