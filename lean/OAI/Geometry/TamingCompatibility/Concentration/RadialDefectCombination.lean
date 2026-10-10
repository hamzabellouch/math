import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FourthMomentKernel
import OAI.Geometry.TamingCompatibility.Charts.RadialUnitCoordinates

namespace OAI

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

theorem exists_defect_combination (hR1 : 2*R ≤ 1) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ δ ≤ R ∧
      ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < δ → ∀ v : Space,
      let β := logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD)) +
        a • sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))
      let val := ManifoldForms.pullback β.val (extChartAt Model p.val).symm y
        ![v,coordinateJ J p.val y v]
      0 ≤ val ∧
        2*hermitianDefect (hermitianCenterExtension J p.val (D p) hφ hc hφD b) (y-b) v /
          (s^2+‖hermitianGraph (hermitianCenterExtension J p.val (D p) hφ hc hφD b) (y-b)‖^2)^2 ≤ val := by
  obtain ⟨C₀,hC₀,hlog⟩ := nonharmonic_logSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters K hK hKU
  obtain ⟨C₁,hC₁,hsqrt⟩ := nonharmonic_sqrtSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 K hK hKU
  let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
  let L := SchwartzMap.seminorm ℝ 0 1 W
  let M := SchwartzMap.seminorm ℝ 0 0 W
  have hL : 0 ≤ L := apply_nonneg _ _
  have hM : 0 ≤ M := apply_nonneg _ _
  let E := (1+M)^2*16*L*M+C₀*M
  let ES := (1+M)^2*10*L*M
  let FS := C₁*M
  let cS := 1/(1+M)
  have hcS : 0 < cS := by dsimp [cS]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨δ,hδ,habs⟩ := exists_inverse_distance_dominates_log cS ES FS hcS
  let a := E/(cS/2)+1
  refine ⟨a,min δ R,by dsimp [a]; positivity,lt_min hδ hR,min_le_right _ _,?_⟩
  intro s hsr b hb y hy hnear v
  dsimp only
  have hsp : 0 < s := hsr.1
  have hball := (hcenters b hb).trans (hKU.trans hUD)
  have hyR : ‖y-b‖ < R := by linarith [(lt_min_iff.mp hnear).2]
  have hone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1 :=
    fun z hz => hφone z (hcenters b hb hz)
  have hl := logForm_defect_lower A J α hs ht H Gs p.val (D p) hφ hc hφD
    hR hsr.1 b y v hball hyR hone hC₀
    (by simpa only [logSource,dist_comm b y,dist_eq_norm] using hlog y hy s hsr b hb)
  have hh := sqrtForm_trace_lower A J α hs ht H Gs p.val (D p) hφ hc hφD
    hR hsr.1 b y v hball hyR hone hC₁
    (by simpa only [sqrtSource,dist_comm b y,dist_eq_norm] using hsqrt y hy s hsr b hb)
  let t := s+‖y-b‖
  have htpos : 0 < t := by dsimp [t]; positivity
  have hsmall : t < δ := (lt_min_iff.mp hnear).1
  have hsa := mul_le_mul_of_nonneg_right (habs t htpos hsmall) (sq_nonneg ‖v‖)
  have hsl : (cS/2)/t*‖v‖^2 ≤
      ManifoldForms.pullback
        (sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
    apply le_trans _ hh
    convert hsa using 1 <;> dsimp only [cS,ES,FS,t,M,L,W] <;>
      simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  let q := 2*hermitianDefect (W b) (y-b) v/(s^2+‖hermitianGraph (W b) (y-b)‖^2)^2
  have hll : q-E/t*‖v‖^2 ≤
      ManifoldForms.pullback
        (logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := hl
  have hcomb := absorb_inverse_distance_error (by positivity : 0 < cS/2) hE htpos hll hsl
  have hsqnonneg := le_trans (by positivity : 0 ≤ (cS/2)/t*‖v‖^2) hsl
  have htotal : q ≤ ManifoldForms.pullback
      (logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] +
      a * ManifoldForms.pullback
      (sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
    dsimp only [a]
    nlinarith
  have hWb : ∀ w, W b (W b w) = -w :=
    hermitianCenterExtension_square J p.val (D p) hφ hc hφD
      (hone b (Metric.mem_closedBall_self (by positivity)))
  have hq : 0 ≤ q := div_nonneg
    (mul_nonneg (by norm_num) (hermitianDefect_nonneg (W b) hWb (y-b) v)) (sq_nonneg _)
  change 0 ≤ _ + a*_ ∧ _
  exact ⟨hq.trans htotal,htotal⟩
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def smoothUnitDefect (p : X) (b : Space) (r s : ℝ) :
    MetricUnit (hermitianMetric J α hs ht) → ℝ :=
  (unitChartDomain J α hs ht p (Metric.closedBall b r)).indicator
    (fun u => 2*unitRadialDefect J α hs ht p b u/(s^2+(unitRadialRadius J α hs ht p b u)^2)^2)

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompactSpace X] [T2Space X] in
lemma smoothUnitDefect_nonneg (p : X) {b : Space} (hb : b ∈ (extChartAt Model p).target)
    (r s : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) :
    0 ≤ smoothUnitDefect J α hs ht p b r s u :=
  Set.indicator_nonneg (fun v _ => div_nonneg
    (mul_nonneg (by norm_num) (unitRadialDefect_nonneg J α hs ht p hb v)) (sq_nonneg _)) u

omit [MeasurableSpace X] [BorelSpace X] in
lemma smoothUnitDefect_integrable (p : X) (b : Space) (r : ℝ) {s : ℝ} (hs' : 0 < s)
    (hball : Metric.closedBall b r ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    Integrable (smoothUnitDefect J α hs ht p b r s) μ := by
  have hc := unitChartDomain_closed J α hs ht p (isCompact_closedBall b r) hball
  apply (integrable_indicator_iff hc.measurableSet).mpr
  apply ContinuousOn.integrableOn_compact hc.isCompact
  exact ((continuousOn_const.mul (unitRadialDefect_continuousOn J α hs ht p b hball)).div
    ((continuousOn_const.add ((unitRadialRadius_continuousOn J α hs ht p b hball).pow 2)).pow 2)
    (fun u _ => by positivity))

variable (A : FiniteCharts X)
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

include hD hH hweak hB hdual hU hUD hτ hρ hφ hc hφD hK hKU hφone hR hK₀ hcenters in

theorem separating_probability_smooth_defect
    (hR1 : 2*R ≤ 1)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r ≤ R ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ K₀,
        ∫ u, smoothUnitDefect J α hs ht p.val b r s u ∂μ ≤ C := by
  obtain ⟨a,δ,ha,hδ,hδR,hpos⟩ := exists_defect_combination
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1
  obtain ⟨C,hC,hglobal⟩ := combinedForm_global_lower
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 a δ ha.le hδ hδR
      (fun s hsr b hb y hy hn v => (hpos s hsr b hb y hy hn v).1)
  let r := δ/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R := by dsimp [r]; linarith
  refine ⟨C,r,hC,hr,hrR,?_⟩
  intro s hsr b hb
  have hsR : s ∈ Ioc (0:ℝ) (2*R) := ⟨hsr.1,hsr.2.trans (hrR.trans (by linarith))⟩
  have hball := (hcenters b hb).trans (hKU.trans hUD)
  have hsmallK : Metric.closedBall b r ⊆ K :=
    (Metric.closedBall_subset_closedBall (hrR.trans (by linarith))).trans (hcenters b hb)
  have hsmallT := hsmallK.trans (hKU.trans (hUD.trans (D p).domain_subset))
  let β := combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b hball
  let f := unitEvaluation J (hermitianMetric J α hs ht) β.val β.property
  have hf : Integrable f μ := f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hz : ∫ u, f u ∂μ = 0 := hann β
    (combinedForm_closed A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b hball
      (harmonicLift_closed A J α hs ht D hD H hH))
    (combinedForm_invariant A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b hball hweak)
  have hle : ∀ u, smoothUnitDefect J α hs ht p.val b r s u ≤ f u+C := by
    intro u
    by_cases hu : u ∈ unitChartDomain J α hs ht p.val (Metric.closedBall b r)
    · rw [smoothUnitDefect,Set.indicator_of_mem hu]
      obtain ⟨hus,hub⟩ := unitChart_mem J α hs ht p.val hsmallT hu
      have hnear : s+‖unitChartBase J α hs ht p.val u-b‖ < δ := by
        have hd : ‖unitChartBase J α hs ht p.val u-b‖ ≤ r := by
          simpa only [Metric.mem_closedBall,dist_eq_norm] using hub
        dsimp [r] at hd hsr
        linarith [hsr.2]
      have hh := (hpos s hsR b hb _ (hsmallK hub) hnear
        (unitChartVector J α hs ht p.val u)).2
      have hW : hermitianCenterExtension J p.val (D p) hφ hc hφD b = coordinateJ J p.val b :=
        hermitianCenterExtension_eq J p.val (D p) hφ hc hφD
          (hφone b ((hcenters b hb) (Metric.mem_closedBall_self (by positivity))))
      rw [hW] at hh
      have hval := unitChart_eval J α hs ht p.val β.val β.property u hus
      change _ = f u at hval
      change 2*unitRadialDefect J α hs ht p.val b u /
        (s^2+(unitRadialRadius J α hs ht p.val b u)^2)^2 ≤ _ at hh
      exact hh.trans (hval.le.trans (le_add_of_nonneg_right hC))
    · rw [smoothUnitDefect,Set.indicator_of_notMem hu]
      have hg := hglobal s hsR b hb u
      change -C ≤ f u at hg
      linarith
  calc
    ∫ u, smoothUnitDefect J α hs ht p.val b r s u ∂μ ≤ ∫ u, (f u+C) ∂μ :=
      integral_mono (smoothUnitDefect_integrable J α hs ht p.val b r hsr.1 hsmallT μ)
        (hf.add (integrable_const C)) hle
    _ = C := by rw [integral_add hf (integrable_const C),hz,integral_const]; simp

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
