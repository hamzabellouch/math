import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.LogErrorAbsorption
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianOff
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCombinedBounds
import OAI.Geometry.TamingCompatibility.Functional.ChartCompactNeighborhood

namespace OAI

section
section

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

theorem combinedForm_global_lower (hR1 : 2*R ≤ 1) (a δ : ℝ) (ha : 0 ≤ a)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hpos : ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < δ → ∀ v : Space,
      0 ≤ ManifoldForms.pullback
        (combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ u : MetricUnit (hermitianMetric J α hs ht),
      let β := combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD));
      -C ≤ unitEvaluation J (hermitianMetric J α hs ht) β.val β.property u := by
  let I := {s : ℝ // s ∈ Ioc (0:ℝ) (2*R)} × K₀
  let β : I → smoothForms X 2 := fun i => combinedForm A J α hs ht H Gs p.val (D p)
    hφ hc hφD a hR i.1.property.1 i.2.val
      ((hcenters i.2.val i.2.property).trans (hKU.trans hUD))
  have hlocal : ∀ x : X, ∃ q : X, ∃ L : Set Space, ∃ C : ℝ,
      0 ≤ C ∧ (∀ᶠ y in 𝓝 x, y ∈ (extChartAt Model q).source ∧ extChartAt Model q y ∈ L) ∧
      ∀ i : I, ∀ z ∈ L, ∀ v : Space, chartMetric J α q z v v = 1 →
        -C ≤ ManifoldForms.pullback (β i).val (extChartAt Model q).symm z ![v,coordinateJ J q z v] := by
    intro x
    by_cases hx : x ∈ (extChartAt Model p.val).symm '' K
    · obtain ⟨z,hz,rfl⟩ := hx
      have hzT := (D p).domain_subset (hUD (hKU hz))
      have hxsrc := (extChartAt Model p.val).map_target hzT
      obtain ⟨L,hL,hLU,hN⟩ := exists_compact_observer_neighborhood p.val hxsrc hU
        (by simpa only [(extChartAt Model p.val).right_inv hzT] using hKU hz)
      obtain ⟨C,hC,hbound⟩ := combinedForm_chart_lower
        A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
        hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 a δ ha hδ hδR hpos L hL hLU
      exact ⟨p.val,L,C,hC,hN,fun i y hy v hv => hbound i.1.val i.1.property i.2.val i.2.property y hy v hv⟩
    · have hclosed : _root_.IsClosed ((extChartAt Model p.val).symm '' K) :=
        (hK.image_of_continuousOn ((continuousOn_extChartAt_symm p.val).mono
          (hKU.trans (hUD.trans (D p).domain_subset)))).isClosed
      obtain ⟨q,hxq,τ',ρ',V,hV,hxV,hVD,hτ',hρ',hoff⟩ :=
        exists_observer_at A J α hs ht D hD hclosed.isOpen_compl hx
      obtain ⟨L,hL,hLV,hN⟩ := exists_compact_observer_neighborhood q.val hxq hV hxV
      obtain ⟨C₀,hC₀,hlog⟩ := logForm_off_source_uniform
        A J α hs ht D hD H Gs hH hweak B hB hdual p τ hφ hc hφD
        K hK (hKU.trans hUD) (fun z hz => hτ z (hKU hz)) hφone R hR K₀ hK₀ hcenters
        q τ' ρ' V hV hVD hτ' hρ' L hL hLV hoff
      obtain ⟨C₁,hC₁,hsqrt⟩ := sqrtForm_off_source_uniform
        A J α hs ht D hD H Gs hH hweak B hB hdual p τ hφ hc hφD
        K hK (hKU.trans hUD) (fun z hz => hτ z (hKU hz)) hφone R hR K₀ hK₀ hcenters
        q τ' ρ' V hV hVD hτ' hρ' L hL hLV hoff
      refine ⟨q.val,L,C₀+a*C₁,by positivity,hN,?_⟩
      intro i z hz v hv
      have hl := hlog i.1.val i.1.property i.2.val i.2.property z hz v hv
      have hh := hsqrt i.1.val i.1.property i.2.val i.2.property z hz v hv
      have hl' := (neg_le_neg hl).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le _)
      have hh' := mul_le_mul_of_nonneg_left ((neg_le_neg hh).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le _)) ha
      calc
        -(C₀+a*C₁) = -C₀+a*(-C₁) := by ring
        _ ≤ _ := add_le_add hl' hh'
  obtain ⟨C,hC,hbound⟩ := compact_family_unit_lower J α hs ht β hlocal
  exact ⟨C,hC,fun s hsr b hb u => hbound (⟨s,hsr⟩,⟨b,hb⟩) u⟩
end TamingCompatibility.GeometricHilbert.Hermitian

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

theorem exists_combined_unit_bounds (hR1 : 2*R ≤ 1) :
    ∃ a c r C : ℝ, 0 < a ∧ 0 < c ∧ 0 < r ∧ r ≤ 2*R ∧ 0 ≤ C ∧
      ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) r, ∀ b, ∀ hb : b ∈ K₀,
      let β := combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))
      (∀ u : MetricUnit (hermitianMetric J α hs ht),
        -C ≤ unitEvaluation J (hermitianMetric J α hs ht) β.val β.property u) ∧
      (∀ u : MetricUnit (hermitianMetric J α hs ht),
        u.val.proj ∈ (extChartAt Model p.val).symm '' Metric.closedBall b s →
        c/s^2 ≤ unitEvaluation J (hermitianMetric J α hs ht) β.val β.property u) := by
  obtain ⟨a,c,δ,ha,hc',hδ,hpos⟩ := exists_positive_combination
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1
  have hnear : ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < min δ R → ∀ v : Space,
      0 ≤ ManifoldForms.pullback
        (combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
    intro s hsr b hb y hy hn v
    exact (hpos s hsr b hb y hy (lt_of_lt_of_le hn (min_le_left _ _)) v).1
  obtain ⟨C,hC,hglobal⟩ := combinedForm_global_lower
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 a (min δ R) ha.le
      (lt_min hδ hR) (min_le_right _ _) hnear
  obtain ⟨m,M,hm,_hM,hmetric⟩ := chartMetric_unit_norm_bounds J α hs ht p.val hK
    (hKU.trans (hUD.trans (D p).domain_subset))
  let r := min R (δ/4)
  have hr : 0 < r := lt_min hR (by positivity)
  have hrR : r ≤ 2*R := (min_le_left R (δ/4)).trans (by linarith)
  refine ⟨a,c*m,r,C,ha,by positivity,hr,hrR,hC,?_⟩
  intro s hsr b hb
  let β := combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))
  have hsR : s ∈ Ioc (0:ℝ) (2*R) := ⟨hsr.1,hsr.2.trans hrR⟩
  refine ⟨hglobal s hsR b hb,?_⟩
  intro u hu
  have hballK : Metric.closedBall b s ⊆ K :=
    (Metric.closedBall_subset_closedBall hsR.2).trans (hcenters b hb)
  obtain ⟨z,hz,hzu⟩ := hu
  have hzT := (D p).domain_subset (hUD (hKU (hballK hz)))
  have huSrc : u.val.proj ∈ (extChartAt Model p.val).source :=
    hzu ▸ (extChartAt Model p.val).map_target hzT
  have he : extChartAt Model p.val u.val.proj = z := by
    rw [← hzu,(extChartAt Model p.val).right_inv hzT]
  apply unitEvaluation_lower_of_chart J α hs ht p.val β.val β.property
    (K := Metric.closedBall b s) ?_ u huSrc (he ▸ hz)
  intro y hy v hv
  have hyd : ‖y-b‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
  have hn : s+‖y-b‖ < δ := by
    have hsd := hsr.2.trans (min_le_right R (δ/4))
    linarith
  have hval := (hpos s hsR b hb y (hballK hy) hn v).2 hyd
  have hmv := (hmetric y (hballK hy) v hv).1
  apply le_trans _ hval
  have hmul := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hmv (sq_nonneg s)) hc'.le
  simpa only [mul_div_assoc] using hmul
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
