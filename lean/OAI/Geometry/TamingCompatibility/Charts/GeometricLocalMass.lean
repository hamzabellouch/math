import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.RiemannianChartControl
import OAI.Geometry.TamingCompatibility.DifferentialForms.PositiveTestMass
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianTestFactory

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open GeometricHilbert GeometricHilbert.Hermitian Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem separating_probability_local_quadratic
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (x : X) :
    ∃ p : X, ∃ R C r : ℝ, x ∈ (extChartAt Model p).source ∧
      0 < R ∧ 0 ≤ C ∧ 0 < r ∧ r ≤ 2*R ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        μ.real {u : MetricUnit (hermitianMetric J α hs ht) |
          u.val.proj ∈ (extChartAt Model p).symm '' Metric.closedBall b s} ≤ C*s^2 := by
  obtain ⟨A,hA⟩ := finite_data_partition J α hs ht
  let D : ∀ p : A.centers, Data J α ht p.val := fun p => data J α hs ht p.val
  obtain ⟨G,H,Gs,hH,_hHclosed,_hGs,hweak,B,hB,hdual⟩ :=
    exists_smooth_inverse_dual_data A J α hs ht D hA
  obtain ⟨p,hp,hz⟩ := exists_nonzero_weight_chart A J α ht D hA x
  have hxsrc := (D p).source_subset (hA p (subset_closure hp))
  have hwz : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxsrc] using hp
  obtain ⟨τ,ρ,φ,U,R,hU,_hzU,hUD,hτ,hρ,hφc,hφD,hR,hR1,hballU,hφone,hcenters⟩ :=
    exists_radial_test_data A J α hs ht D p hz hwz
  obtain ⟨C,r,hC,hr,hrR,hmass⟩ := separating_probability_chart_mass
    A J α hs ht D hA H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    (φ.smooth ⊤) hφc hφD (Metric.closedBall (extChartAt Model p.val x) (4*R))
    (isCompact_closedBall _ _) hballU hφone R hR
    (Metric.closedBall (extChartAt Model p.val x) R) (isCompact_closedBall _ _) hcenters hR1 μ hann
  exact ⟨p.val,R,C,r,hxsrc,hR,hC,hr,hrR,hballU.trans (hUD.trans (D p).domain_subset),hmass⟩
end TamingCompatibility

end
end

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold Set MeasureTheory Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]

theorem local_chart_mass_to_riemannian {Y : Type*} [MeasurableSpace Y]
    (proj : Y → X) (μ : Measure Y) [IsProbabilityMeasure μ]
    (hloc : ∀ x : X, ∃ p : X, ∃ R C r : ℝ,
      x ∈ (extChartAt Model p).source ∧ 0 < R ∧ 0 ≤ C ∧ 0 < r ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        μ.real {u : Y | proj u ∈ (extChartAt Model p).symm '' Metric.closedBall b s} ≤ C*s^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^2 := by
  let : EMetricSpace X := .ofRiemannianMetric Model X
  let P := fun (x : X) (C : ℝ) => ∀ s : ℝ, 0 < s →
    μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^2
  suffices hlocal : ∀ x ∈ (univ : Set X), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, P y C by
    obtain ⟨C,hC,hbound⟩ := _root_.OAI.IsCompact.exists_uniform_monotone_bound (isCompact_univ : IsCompact (univ : Set X))
      P (fun _ a b hab ha s hs => (ha s hs).trans
        (mul_le_mul_of_nonneg_right hab (sq_nonneg s))) hlocal
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
  have hCL : 0 ≤ C*(L:ℝ)^2 := mul_nonneg hC (sq_nonneg _)
  let D : ℝ := C*(L:ℝ)^2 + 1/q^2
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
      _ ≤ C*((L:ℝ)*s)^2 := hmass _ ⟨mul_pos hLp hs,hsLr⟩ _ (Metric.ball_subset_closedBall hy.2)
      _ = (C*(L:ℝ)^2)*s^2 := by ring
      _ ≤ D*s^2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (sq_nonneg s)
  · have hqs : q ≤ s := le_of_lt (lt_of_not_ge hsq)
    have hpow : q^2 ≤ s^2 := pow_le_pow_left₀ hq.le hqs 2
    have hlarge : 1 ≤ (1/q^2)*s^2 := by
      rw [one_div,inv_mul_eq_div]
      exact (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by simpa using hpow)
    exact measureReal_le_one.trans (hlarge.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCL) (sq_nonneg s)))
end TamingCompatibility

end
end

end
end

end OAI
