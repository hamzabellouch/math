import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScalarWedgeBounds
import OAI.Geometry.TamingCompatibility.Functional.CompactPairingBound

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory Hermitian Concentration ContinuousAlternatingMap
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma concentrationPatch_differential_chart
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) {z : Space} (hz : z ∈ (extChartAt Model p.val).target) :
    ManifoldForms.pullback (scalarDifferential (concentrationPatch A J α hs ht E μ p r))
      (extChartAt Model p.val).symm z =
      ofSubsingletonLIE (0 : Fin 1)
        (localConcentration A J α hs ht E μ p r z • fderiv ℝ (coordinatePartition A p) z+
          coordinatePartition A p z • fderiv ℝ (localConcentration A J α hs ht E μ p r) z) := by
  rw [pullback_scalarDifferential
    ((concentrationPatch_smooth A J α hs ht E μ p hr).mdifferentiable (by simp) _)
    (((contMDiffOn_extChartAt_symm (n := ∞) p.val) z hz).contMDiffAt
      ((isOpen_extChartAt_target p.val).mem_nhds hz) |>.mdifferentiableAt (by simp))]
  unfold concentrationPatch
  rw [scalarChartLift_fderiv p.val _ hz]
  congr 1
  simpa only [Pi.mul_apply,add_comm] using fderiv_fun_mul ((coordinatePartition_smooth_compact A p).1.differentiable (by simp) z)
    ((localConcentration_smooth A J α hs ht E μ p hr).differentiable (by simp) z)

omit [T2Space X] [CompactSpace X] in
lemma concentrationPatch_differential_zero_off
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (p : A.centers) (r : ℝ)
    {x : X} (hx : x ∉ tsupport (A.partition p)) :
    scalarDifferential (concentrationPatch A J α hs ht E μ p r) x = 0 := by
  have he : concentrationPatch A J α hs ht E μ p r =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have hopen : IsOpen ((tsupport (A.partition p))ᶜ) := (isClosed_tsupport _).isOpen_compl
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [concentrationPatch_apply, image_eq_zero_of_notMem_tsupport (f := (A.partition p : X → ℝ)) hy,zero_mul]
  unfold scalarDifferential
  rw [he.mfderiv_eq,mfderiv_const]
  change (ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)) (0 : Space →L[ℝ] ℝ) = 0
  exact _root_.map_zero _

omit [T2Space X] [CompactSpace X] in
lemma concentrationPatch_wedge_zero_off
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (p : A.centers) (r : ℝ)
    (θ : Form X 1) {x : X} (hx : x ∉ tsupport (A.partition p)) :
    ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ x = 0 := by
  unfold ManifoldForms.wedgeOne
  rw [concentrationPatch_differential_zero_off A J α hs ht E μ p r hx]
  change ExteriorForms.wedgeOne ((ofSubsingletonLIE (0 : Fin 1)).symm (0 : ExteriorForms.Form (E := Space) 1)) _ = _
  rw [_root_.map_zero]
  exact (ExteriorForms.wedgeOneRight (E := Space) (θ x)).map_zero

lemma concentrationPatch_wedge_chart
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) (θ : Form X 1)
    {z : Space} (hz : z ∈ (extChartAt Model p.val).target) :
    ManifoldForms.pullback
      (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ)
      (extChartAt Model p.val).symm z =
      ExteriorForms.wedgeOne
        (localConcentration A J α hs ht E μ p r z • fderiv ℝ (coordinatePartition A p) z+
          coordinatePartition A p z • fderiv ℝ (localConcentration A J α hs ht E μ p r) z)
        (ManifoldForms.pullback θ (extChartAt Model p.val).symm z) := by
  rw [ManifoldForms.pullback_wedgeOne]
  dsimp only
  rw [concentrationPatch_differential_chart A J α hs ht E μ p hr hz]
  congr 1

omit [T2Space X] [CompactSpace X] in
lemma concentration_theta_bound (p : A.centers) (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ (E p).concentrationCompact,
      ‖ManifoldForms.pullback θ.val (extChartAt Model p.val).symm z‖ ≤ C := by
  obtain ⟨C,hC⟩ := (E p).concentrationCompact_compact.exists_bound_of_continuousOn
    ((smooth_chart θ.val θ.property p.val).continuousOn.mono (E p).concentrationCompact_target)
  exact ⟨max C 0,le_max_right _ _,fun z hz => (hC z hz).trans (le_max_left _ _)⟩

omit [T2Space X] in
lemma concentration_partition_derivative_bound (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ (E p).concentrationCompact,
      ‖fderiv ℝ (coordinatePartition A p) z‖ ≤ C := by
  obtain ⟨C,hC⟩ := (E p).concentrationCompact_compact.exists_bound_of_continuousOn
    (((coordinatePartition_smooth_compact A p).1.continuous_fderiv (by simp)).continuousOn)
  exact ⟨max C 0,le_max_right _ _,fun z hz => (hC z hz).trans (le_max_left _ _)⟩
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory Hermitian Concentration ContinuousAlternatingMap
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
lemma concentrationPatch_tangential_bound (p : A.centers) (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
      [IsFiniteMeasure μ], ∀ r : ℝ, ∀ hr : 0 < r,
      ∀ u : MetricUnit (hermitianMetric J α hs ht), u.val.proj ∈ tsupport (A.partition p) →
      |unitEvaluation J (hermitianMetric J α hs ht)
        (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
        ((scalarDifferential_smooth (concentrationPatch_smooth A J α hs ht E μ p hr)).wedgeOne θ.property) u| ≤
      C*(localConcentration A J α hs ht E μ p r (unitChartBase J α hs ht p.val u)+
        A.partition p u.val.proj *
          (|fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartFirst J α hs ht p.val u)|+
           |fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)|)) := by
  obtain ⟨B,hB,hθ⟩ := concentration_theta_bound A J α ht E p θ
  obtain ⟨D,hD,hd⟩ := concentration_partition_derivative_bound A J α ht E p
  obtain ⟨_,M,_,hM,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  refine ⟨M*B*(2*D+1),by positivity,fun μ _ r hr u hx => ?_⟩
  have hu := unitChartPlane J α hs ht p.val u (A.subordinate p hx)
  have hz := (E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)
  have htgt := (E p).concentrationCompact_target hz
  have huK : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact :=
    ⟨_,hz,(extChartAt Model p.val).left_inv (A.subordinate p hx)⟩
  let z := unitChartBase J α hs ht p.val u
  let f := localConcentration A J α hs ht E μ p r
  let χ := A.partition p u.val.proj
  let d := fderiv ℝ (coordinatePartition A p) z
  let l := fderiv ℝ f z
  have hf : 0 ≤ f z := localConcentration_nonneg A J α hs ht E μ p r z
  have hχ : 0 ≤ χ := A.partition.nonneg _ _
  have hw : |(f z • d+χ • l) (unitChartFirst J α hs ht p.val u)| ≤ f z*D+χ*|l (unitChartFirst J α hs ht p.val u)| := by
    have hh : |d (unitChartFirst J α hs ht p.val u)| ≤ D := by
      have h := d.le_opNorm (unitChartFirst J α hs ht p.val u)
      rw [hu.1,mul_one] at h
      exact h.trans (hd z hz)
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
    exact (abs_add_le _ _).trans (by rw [abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg hχ]; gcongr)
  have hv : |(f z • d+χ • l) (unitChartSecond J α hs ht p.val u)| ≤ f z*D+χ*|l (unitChartSecond J α hs ht p.val u)| := by
    have hh : |d (unitChartSecond J α hs ht p.val u)| ≤ D := by
      have h := d.le_opNorm (unitChartSecond J α hs ht p.val u)
      rw [hu.2.1,mul_one] at h
      exact h.trans (hd z hz)
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
    exact (abs_add_le _ _).trans (by rw [abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg hχ]; gcongr)
  have heval := unitChartArea_eval J α hs ht p.val
    (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
    ((scalarDifferential_smooth (concentrationPatch_smooth A J α hs ht E μ p hr)).wedgeOne θ.property) u (A.subordinate p hx)
  change eval _ u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) = _ at heval
  change |eval _ u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤ _
  rw [heval]
  dsimp only [unitChartBase]
  rw [concentrationPatch_wedge_chart A J α hs ht E μ p hr θ.val htgt,
    coordinatePartition_apply A p (A.subordinate p hx),abs_mul,abs_of_pos hu.2.2.2]
  have hh := ExteriorForms.scalar_wedge_unit (f z • d+χ • l)
    (ManifoldForms.pullback θ.val (extChartAt Model p.val).symm z)
    (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u) hu.1 hu.2.1
  have hh' : |ExteriorForms.wedgeOne (f z • d+χ • l)
      (ManifoldForms.pullback θ.val (extChartAt Model p.val).symm z)
      ![unitChartFirst J α hs ht p.val u,unitChartSecond J α hs ht p.val u]| ≤
      B*(2*D*(f z)+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|)) := by
    exact hh.trans ((mul_le_mul (hθ z hz) (add_le_add hw hv) (by positivity) hB).trans_eq (by ring))
  have hb := mul_le_mul (harea u huK).2 hh' (abs_nonneg _) hM.le
  have hn : 0 ≤ χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|) := by positivity
  have hbb : 0 ≤ M*B := by positivity
  have he : 2*D*(f z)+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|) ≤
      (2*D+1)*(f z+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|)) := by nlinarith
  calc
    _ ≤ M*(B*(2*D*(f z)+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|))) := hb
    _ = (M*B)*(2*D*(f z)+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|)) := by ring
    _ ≤ (M*B)*((2*D+1)*(f z+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|))) := mul_le_mul_of_nonneg_left he hbb
    _ = _ := by dsimp only [f,z,l,χ,unitChartBase]; ring

include hE in
lemma concentrationPatch_coefficient_bound (p : A.centers) (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
      [IsFiniteMeasure μ], ∀ r : ℝ, ∀ _hr : 0 < r,
      ∀ x : X, x ∈ tsupport (A.partition p) →
      ‖normalizedFrameEncode A J α ht E x
        (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val x)‖ ≤
      C*(localConcentration A J α hs ht E μ p r (extChartAt Model p.val x)+
        A.partition p x*‖fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x)‖) := by
  obtain ⟨B,hB,hθ⟩ := concentration_theta_bound A J α ht E p θ
  obtain ⟨D,hD,hd⟩ := concentration_partition_derivative_bound A J α ht E p
  obtain ⟨M,hM,hcoef⟩ := normalizedFrameEncode_chart_bound A J α ht E hE p
  refine ⟨M*2*B*(D+1),by positivity,fun μ _ r hr x hx => ?_⟩
  have hz := (E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)
  have htgt := (E p).concentrationCompact_target hz
  let z := extChartAt Model p.val x
  let f := localConcentration A J α hs ht E μ p r
  have hf : 0 ≤ f z := localConcentration_nonneg A J α hs ht E μ p r z
  have hχ := A.partition.nonneg p x
  have hnorm : ‖f z • fderiv ℝ (coordinatePartition A p) z+A.partition p x • fderiv ℝ f z‖ ≤
      f z*D+A.partition p x*‖fderiv ℝ f z‖ := by
    calc
      _ ≤ ‖f z • fderiv ℝ (coordinatePartition A p) z‖+‖A.partition p x • fderiv ℝ f z‖ := norm_add_le _ _
      _ = f z*‖fderiv ℝ (coordinatePartition A p) z‖+A.partition p x*‖fderiv ℝ f z‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hf,abs_of_nonneg hχ]
      _ ≤ _ := by gcongr; exact hd z hz
  have hh := hcoef (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val) z hz
  rw [(extChartAt Model p.val).left_inv (A.subordinate p hx)] at hh
  rw [concentrationPatch_wedge_chart A J α hs ht E μ p hr θ.val htgt,
    coordinatePartition_apply A p (A.subordinate p hx)] at hh
  have hw := ExteriorForms.scalar_wedge_norm
    (f z • fderiv ℝ (coordinatePartition A p) z+A.partition p x • fderiv ℝ f z)
    (ManifoldForms.pullback θ.val (extChartAt Model p.val).symm z)
  have hb := hh.trans (mul_le_mul_of_nonneg_left
    (hw.trans (mul_le_mul (mul_le_mul_of_nonneg_left hnorm (by norm_num)) (hθ z hz) (norm_nonneg _) (by positivity))) hM)
  have hb' : 0 ≤ M*2*B := by positivity
  have he : f z*D+A.partition p x*‖fderiv ℝ f z‖ ≤
      (D+1)*(f z+A.partition p x*‖fderiv ℝ f z‖) := by nlinarith [mul_nonneg hχ (norm_nonneg (fderiv ℝ f z))]
  calc
    _ ≤ M*(2*(f z*D+A.partition p x*‖fderiv ℝ f z‖)*B) := hb
    _ = (M*2*B)*(f z*D+A.partition p x*‖fderiv ℝ f z‖) := by ring
    _ ≤ (M*2*B)*((D+1)*(f z+A.partition p x*‖fderiv ℝ f z‖)) := mul_le_mul_of_nonneg_left he hb'
    _ = _ := by dsimp only [f,z]; ring
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
