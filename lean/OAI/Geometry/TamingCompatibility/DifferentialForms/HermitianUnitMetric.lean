import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.CompactUniformBound
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianFarSmooth
import OAI.Geometry.TamingCompatibility.Functional.CompactPositiveBilinear

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldVolume
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J)

include hs ht in
lemma chartMetric_compact_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : Space,
      m*‖v‖^2 ≤ chartMetric J α p z v v ∧ chartMetric J α p z v v ≤ M*‖v‖^2 :=
  compact_positive_bilinear_bounds hK (((hs.invariantPart J).metricCoords J p).continuousOn.mono hKT)
    (fun _z hz v hv => chartMetric_pos J α ht p (hKT hz) v hv)

include hs ht in
lemma chartMetric_unit_norm_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : Space,
      chartMetric J α p z v v = 1 → m ≤ ‖v‖^2 ∧ ‖v‖^2 ≤ M := by
  obtain ⟨a,b,ha,hb,hbound⟩ := chartMetric_compact_bounds J α hs ht p hK hKT
  refine ⟨1/b,1/a,by positivity,by positivity,?_⟩
  intro z hz v hv
  obtain ⟨hlo,hup⟩ := hbound z hz v
  rw [hv] at hlo hup
  exact ⟨(div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hup),
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hlo)⟩

include ht in
lemma chartMetric_hermitian (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z (coordinateJ J p z u) (coordinateJ J p z v) =
      chartMetric J α p z u v := by
  have h := coordinateMetric_hermitian J α ht p hz u v
  simpa only [coordinateMetric_bilinear J α ht p hz] using h

include hs ht in
lemma form_unit_line_bound (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, ∀ v : Space, chartMetric J α p z v v = 1 →
      ∀ β : MetricForms.Form Space 2, ‖β ![v,coordinateJ J p z v]‖ ≤ ‖β‖*M := by
  obtain ⟨m,M,_,hM,hbound⟩ := chartMetric_unit_norm_bounds J α hs ht p hK hKT
  refine ⟨M,hM,?_⟩
  intro z hz v hv β
  have hnv := (hbound z hz v hv).2
  have hnJ := (hbound z hz (coordinateJ J p z v)
    ((chartMetric_hermitian J α ht p (hKT hz) v v).trans hv)).2
  have hprod : ‖v‖*‖coordinateJ J p z v‖ ≤ M := by
    nlinarith [sq_nonneg (‖v‖-‖coordinateJ J p z v‖)]
  calc
    _ ≤ ‖β‖*(‖v‖*‖coordinateJ J p z v‖) := by
      simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
        using β.le_opNorm ![v,coordinateJ J p z v]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)

lemma inverse_coordinates_eval (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (β : TwoForm X) (u : TangentSpace Model ((extChartAt Model p).symm z)) :
    ∃ v : Space,
      chartMetric J α p z v v = (hermitianMetric J α hs ht).inner _ u u ∧
      ManifoldForms.pullback β (extChartAt Model p).symm z ![v,coordinateJ J p z v] =
        eval β ((extChartAt Model p).symm z) u (J.endomorphism _ u) := by
  let L := inverseChartEquiv p z hz
  have he : mfderiv Model Model (extChartAt Model p).symm z (L.symm u) = u := by
    rw [← inverseChartEquiv_coe p z hz]
    exact L.apply_symm_apply u
  refine ⟨L.symm u,?_,?_⟩
  · rw [chartMetric_derivative J α p hz,he]
    rfl
  · rw [pullback_complexLine J β p hz,he]

lemma unitEvaluation_lower_of_chart (p : X) {K : Set Space} {c : ℝ}
    (β : TwoForm X) (hβ : IsSmooth β)
    (hbound : ∀ z ∈ K, ∀ v : Space, chartMetric J α p z v v = 1 →
      c ≤ ManifoldForms.pullback β (extChartAt Model p).symm z ![v,coordinateJ J p z v])
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source)
    (hzK : extChartAt Model p u.val.proj ∈ K) :
    c ≤ unitEvaluation J (hermitianMetric J α hs ht) β hβ u := by
  let z := extChartAt Model p u.val.proj
  have hz : z ∈ (extChartAt Model p).target := (extChartAt Model p).map_source hu
  have hb : ∀ w : TangentSpace Model ((extChartAt Model p).symm z),
      (hermitianMetric J α hs ht).inner _ w w = 1 →
      c ≤ eval β ((extChartAt Model p).symm z) w (J.endomorphism _ w) := by
    intro w hw
    obtain ⟨v,hv,he⟩ := inverse_coordinates_eval J α hs ht p hz β w
    exact he ▸ hbound z hzK v (hv.trans hw)
  have hbase : (extChartAt Model p).symm z = u.val.proj := (extChartAt Model p).left_inv hu
  rw [hbase] at hb
  exact hb u.val.2 u.property
end TamingCompatibility.ManifoldVolume

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in

theorem logForm_far_uniform (L : Set Space) (hL : IsCompact L)
    (hLU : L ⊆ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ L, ε ≤ s+‖y-b‖ → ∀ v : Space, chartMetric J α p.val y v v = 1 →
      ‖ManifoldForms.pullback
        (logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤ C := by
  let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
  have hLT : L ⊆ (extChartAt Model p.val).target := hLU.trans (hUD.trans (D p).domain_subset)
  obtain ⟨C₀,hC₀,hraw⟩ := HermitianRadial.cutoffLog_ddc_far_bound
    W (W.smooth ⊤) (coordinateJ J p.val) (extChartAt Model p.val).target
    (isOpen_extChartAt_target p.val) (coordinateJ_smooth J p.val)
    R K₀ L hK₀ hL hLT ε hε
  obtain ⟨C₁,hC₁,hcorr⟩ := nonharmonic_logSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters L hL hLU
  let F := C₁/ε
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨M,hM,hunit⟩ := form_unit_line_bound J α hs ht p.val hL hLT
  refine ⟨(C₀+F)*M,by positivity,?_⟩
  intro s hsr b hb y hy hfar v hv
  have hball := (hcenters b hb).trans (hKU.trans hUD)
  have hnc : ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
      (logSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b hball)‖ ≤ F := by
    exact (hcorr y hy s hsr b hb).trans
      (div_le_div_of_nonneg_left hC₁ hε (by simpa only [dist_comm b y,dist_eq_norm] using hfar))
  have hrc := hraw s ⟨hsr.1.le,hsr.2⟩ b hb y hy hfar
  rw [logForm,correctedDdc_pullback_complexLine A J α hs ht H Gs _ p.val (hLT hy),
    pullback_ddc_scalarChartLift J p.val
      (HermitianRadial.translatedCutoffLog_smooth W R hsr.1 b)
      (HermitianRadial.translatedCutoffLog_compact W hR s b)
      (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hball).trans
        (D p).domain_subset) (hLT hy)]
  calc
    _ ≤ ‖extDeriv (ExteriorForms.dc (coordinateJ J p.val)
        (HermitianRadial.translatedCutoffLog W R s b)) y ![v,coordinateJ J p.val y v]‖ +
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (logSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b hball)
        ![v,coordinateJ J p.val y v]‖ := norm_sub_le _ _
    _ ≤ C₀*M+F*M := add_le_add
      ((hunit y hy v hv _).trans (mul_le_mul_of_nonneg_right hrc hM.le))
      ((hunit y hy v hv _).trans (mul_le_mul_of_nonneg_right hnc hM.le))
    _ = _ := by ring

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in

theorem sqrtForm_far_uniform (hR1 : 2*R ≤ 1) (L : Set Space) (hL : IsCompact L)
    (hLU : L ⊆ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ L, ε ≤ s+‖y-b‖ → ∀ v : Space, chartMetric J α p.val y v v = 1 →
      ‖ManifoldForms.pullback
        (sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤ C := by
  let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
  have hLT : L ⊆ (extChartAt Model p.val).target := hLU.trans (hUD.trans (D p).domain_subset)
  obtain ⟨C₀,hC₀,hraw⟩ := HermitianRadial.cutoffSqrt_ddc_far_bound
    W (W.smooth ⊤) (coordinateJ J p.val) (extChartAt Model p.val).target
    (isOpen_extChartAt_target p.val) (coordinateJ_smooth J p.val)
    R K₀ L hK₀ hL hLT ε hε
  obtain ⟨C₁,hC₁,hcorr⟩ := nonharmonic_sqrtSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 L hL hLU
  obtain ⟨C₂,hC₂,hlog⟩ := HermitianRadial.log_distance_far_bound R K₀ L hK₀ hL ε hε
  let F := C₁*(1+C₂)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨M,hM,hunit⟩ := form_unit_line_bound J α hs ht p.val hL hLT
  refine ⟨(C₀+F)*M,by positivity,?_⟩
  intro s hsr b hb y hy hfar v hv
  have hball := (hcenters b hb).trans (hKU.trans hUD)
  have hnc : ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
      (sqrtSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b hball)‖ ≤ F := by
    apply (hcorr y hy s hsr b hb).trans
    apply mul_le_mul_of_nonneg_left _ hC₁
    simpa only [dist_comm b y,dist_eq_norm,add_comm] using
      add_le_add_left (hlog s ⟨hsr.1.le,hsr.2⟩ b hb y hy hfar) 1
  have hrc := hraw s ⟨hsr.1.le,hsr.2⟩ b hb y hy hfar
  rw [sqrtForm,correctedDdc_pullback_complexLine A J α hs ht H Gs _ p.val (hLT hy),
    pullback_ddc_scalarChartLift J p.val
      (HermitianRadial.translatedCutoffSqrt_smooth W R hsr.1 b)
      (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
      (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hball).trans
        (D p).domain_subset) (hLT hy)]
  calc
    _ ≤ ‖extDeriv (ExteriorForms.dc (coordinateJ J p.val)
        (HermitianRadial.translatedCutoffSqrt W R s b)) y ![v,coordinateJ J p.val y v]‖ +
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (sqrtSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b hball)
        ![v,coordinateJ J p.val y v]‖ := norm_sub_le _ _
    _ ≤ C₀*M+F*M := add_le_add
      ((hunit y hy v hv _).trans (mul_le_mul_of_nonneg_right hrc hM.le))
      ((hunit y hy v hv _).trans (mul_le_mul_of_nonneg_right hnc hM.le))
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
