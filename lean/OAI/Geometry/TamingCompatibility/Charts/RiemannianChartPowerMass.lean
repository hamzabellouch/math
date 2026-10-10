import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.RiemannianChartControl
import OAI.Geometry.TamingCompatibility.DifferentialForms.PositiveTestMass

namespace OAI

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold Set MeasureTheory Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]

theorem local_chart_mass_power_to_riemannian {Y : Type*} [MeasurableSpace Y]
    (proj : Y → X) (μ : Measure Y) [IsFiniteMeasure μ] (n : ℕ)
    (hloc : ∀ x : X, ∃ p : X, ∃ R C r : ℝ,
      x ∈ (extChartAt Model p).source ∧ 0 < R ∧ 0 ≤ C ∧ 0 < r ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        μ.real {u : Y | proj u ∈ (extChartAt Model p).symm '' Metric.closedBall b s} ≤ C*s^n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^n := by
  let : EMetricSpace X := .ofRiemannianMetric Model X
  let P := fun (x : X) (C : ℝ) => ∀ s : ℝ, 0 < s →
    μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^n
  suffices hlocal : ∀ x ∈ (univ : Set X), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, P y C by
    obtain ⟨C,hC,hbound⟩ := _root_.OAI.IsCompact.exists_uniform_monotone_bound (isCompact_univ : IsCompact (univ : Set X))
      P (fun _ a b hab ha s hs => (ha s hs).trans
        (mul_le_mul_of_nonneg_right hab (pow_nonneg hs.le n))) hlocal
    exact ⟨C,hC,fun x => hbound x (mem_univ x)⟩
  intro x _hx
  obtain ⟨p,R,C,r,hxs,hR,hC,hr,h4,hmass⟩ := hloc x
  let e := extChartAt Model p
  have h2 : Metric.closedBall (e x) (2*R) ⊆ e.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans h4
  have h1 : Metric.closedBall (e x) R ⊆ e.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans h4
  let K := e.symm '' Metric.closedBall (e x) R
  let W := e.source ∩ e ⁻¹' Metric.ball (e x) (2*R)
  let V := e.source ∩ e ⁻¹' Metric.ball (e x) R
  have hK : IsCompact K := inverse_chart_compact_image p (isCompact_closedBall _ _) h1
  have hW : IsOpen W := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hV : IsOpen V := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hxs,by simpa using hR⟩
  have hKW : K ⊆ W := by
    rintro y ⟨z,hz,rfl⟩
    have hzt := h1 hz
    refine ⟨e.map_target hzt,?_⟩
    change dist (e (e.symm z)) (e x) < 2*R
    rw [e.right_inv hzt]
    exact lt_of_le_of_lt hz (by linarith)
  obtain ⟨δ,hδ,hδW⟩ := hK.exists_thickening_subset_open hW hKW
  obtain ⟨L,hL,hbound⟩ := compact_chart_distance_control p (isCompact_closedBall (e x) (2*R)) h2
  let q : ℝ := min δ (r/L)
  have hLp : (0:ℝ) < L := hL
  have hq : 0 < q := lt_min hδ (div_pos hr hLp)
  have hCL : 0 ≤ C*(L:ℝ)^n := mul_nonneg hC (pow_nonneg L.coe_nonneg n)
  let D : ℝ := C*(L:ℝ)^n + μ.real univ/q^n
  have hD : 0 ≤ D := add_nonneg hCL (by positivity)
  refine ⟨D,hD,?_⟩
  filter_upwards [hV.mem_nhds hxV] with y hy
  intro s hs
  by_cases hsq : s ≤ q
  · have hsδ : s ≤ δ := hsq.trans (min_le_left _ _)
    have hsLr : (L:ℝ)*s ≤ r := by
      have ht := (le_div_iff₀ hLp).mp (hsq.trans (min_le_right _ _))
      simpa only [mul_comm] using ht
    have hyK : y ∈ K := ⟨e y,Metric.ball_subset_closedBall hy.2,e.left_inv hy.1⟩
    have hy2 : e y ∈ Metric.closedBall (e x) (2*R) :=
      (Metric.closedBall_subset_closedBall (by linarith)) (Metric.ball_subset_closedBall hy.2)
    have hsub : {u : Y | riemannianEDist Model y (proj u) < ENNReal.ofReal s} ⊆
        {u : Y | proj u ∈ e.symm '' Metric.closedBall (e y) ((L:ℝ)*s)} := by
      intro u hu
      have huδ : edist (proj u) y < ENNReal.ofReal δ := by
        rw [edist_comm]
        exact hu.trans_le (ENNReal.ofReal_le_ofReal hsδ)
      have huW : proj u ∈ W := hδW ((Metric.mem_thickening_iff_exists_edist_lt K (proj u)).mpr ⟨y,hyK,huδ⟩)
      have hc := hbound y (proj u) hy.1 huW.1 hy2 (Metric.ball_subset_closedBall huW.2)
      have hcoord : dist (e (proj u)) (e y) ≤ (L:ℝ)*s := by
        apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg L.coe_nonneg hs.le)).mp
        rw [ENNReal.ofReal_mul L.coe_nonneg,ENNReal.ofReal_coe_nnreal,← edist_dist,edist_comm]
        exact hc.trans (by gcongr; exact hu.le)
      exact ⟨e (proj u),hcoord,e.left_inv huW.1⟩
    calc
      _ ≤ μ.real {u : Y | proj u ∈ e.symm '' Metric.closedBall (e y) ((L:ℝ)*s)} := measureReal_mono hsub
      _ ≤ C*((L:ℝ)*s)^n := hmass _ ⟨mul_pos hLp hs,hsLr⟩ _ (Metric.ball_subset_closedBall hy.2)
      _ = (C*(L:ℝ)^n)*s^n := by rw [mul_pow,mul_assoc]
      _ ≤ D*s^n := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (pow_nonneg hs.le n)
  · have hqs : q ≤ s := le_of_lt (lt_of_not_ge hsq)
    have hpow : q^n ≤ s^n := pow_le_pow_left₀ hq.le hqs n
    have hlarge : μ.real univ ≤ (μ.real univ/q^n)*s^n := by
      rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hq n)]
      exact mul_le_mul_of_nonneg_left hpow (measureReal_nonneg)
    exact (measureReal_mono (subset_univ _)).trans (hlarge.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCL) (pow_nonneg hs.le n)))
end TamingCompatibility

end
end

end OAI
