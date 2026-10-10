import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalInverseCompact
import OAI.Geometry.TamingCompatibility.DifferentialForms.EuclideanAngularDomain

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable
include hE in
omit [SecondCountableTopology X] in
lemma euclidean_angular_near_point (p : A.centers) :
    ∃ C B L ρ : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ 0 < L ∧ 0 < ρ ∧
      ∀ s : ℝ, 0 < s → s ≤ ρ → ∀ uv : UnitPair J α hs ht,
      euclideanAngularNear A J α hs ht E s p uv ≤ C*angularNear A J α hs ht E (L*s) p uv +
        B*s^2*(euclideanNearSet A J α hs ht E s p).indicator (fun _ => (1:ℝ)) uv := by
  obtain ⟨C,hC,r,hr,hang⟩ := euclidean_angular_point A J α hs ht E hE p
  obtain ⟨L,hL,ε,hε,hinv⟩ := (E p).normal_inverse_near
  let ρ := min ε (r/L)
  have hρ : 0 < ρ := lt_min hε (div_pos hr hL)
  refine ⟨2*C ^ 2,2*C ^ 2*L^2,L,ρ,by positivity,by positivity,hL,hρ,fun s hs' hsρ uv => ?_⟩
  by_cases huv : uv ∈ euclideanNearSet A J α hs ht E s p
  · have hz := angularCoordinates_mem A J α hs ht E p huv.1
    have he := angularCoordinates_chart A J α hs ht E p huv.1
    have he1 := congrArg Prod.fst he
    change (angularCoordinates A J α hs ht E p uv).1 = (angularChartCoordinates A J α hs ht p uv).1 at he1
    have hq : (angularChartCoordinates A J α hs ht p uv).1 ∈ Metric.closedBall
        (extChartAt Model p.val p.val) (E p).radius := by rw [← he1]; exact hz.1
    have hi := hinv _ hq _ (huv.2.trans (hsρ.trans (min_le_left _ _)))
    have hn : ‖(angularCoordinates A J α hs ht E p uv).2‖ ≤ L*s :=
      hi.2.1.trans (mul_le_mul_of_nonneg_left huv.2 hL.le)
    have hnr : ‖(angularCoordinates A J α hs ht E p uv).2‖ ≤ r := by
      apply hn.trans
      simpa only [mul_comm] using (le_div_iff₀ hL).mp (hsρ.trans (min_le_right _ _))
    have ha := hang uv huv.1 hnr
    have ha0 : 0 ≤ normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2 := norm_nonneg _
    have hnorm0 : 0 ≤ ‖(angularCoordinates A J α hs ht E p uv).2‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have hn2 := pow_le_pow_left₀ hnorm0 hn 2
    have htwo := sq_nonneg (normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2 -
      ‖(angularCoordinates A J α hs ht E p uv).2‖)
    have hh : ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2 ≤
        2*C ^ 2*(normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2)^2 +
          2*C ^ 2*L^2*s^2 := by
      nlinarith [mul_nonneg (sq_nonneg C) htwo,mul_le_mul_of_nonneg_left hn2 (sq_nonneg C)]
    have hpart0 := A.partition.nonneg p uv.2.val.proj
    have hpart1 := A.partition.le_one p uv.2.val.proj
    have hmul := mul_le_mul_of_nonneg_left hh hpart0
    have hlast := mul_le_mul_of_nonneg_right hpart1 (by positivity : 0 ≤ 2*C ^ 2*L^2*s^2)
    have hangmem : uv ∈ angularNearSet A J α hs ht E (L*s) p := ⟨huv.1,hn⟩
    rw [euclideanAngularNear,indicator_of_mem huv,angularNear,indicator_of_mem hangmem,indicator_of_mem huv]
    dsimp only [euclideanAngularWeight,angularWeight]
    have hep : coordinatePartition A p (angularCoordinates A J α hs ht E p uv).1 = A.partition p uv.2.val.proj := by
      rw [he1]
      exact coordinatePartition_apply A p (angularChartCoordinates_source A J α hs ht E p huv.1).1
    have hec : (E p).normalCutoff (angularCoordinates A J α hs ht E p uv).2 = 1 := hi.2.2
    rw [hep,hec]
    nlinarith
  · rw [euclideanAngularNear,indicator_of_notMem huv,indicator_of_notMem huv,mul_zero,add_zero]
    exact mul_nonneg (by positivity) (angularNear_nonneg A J α hs ht E (L*s) p uv)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanLine_norm (p : A.centers) (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source) : ‖euclideanLine A J α hs ht p u‖ = 1 := by
  obtain ⟨h1,h2,h3,_⟩ := unitChartPlane J α hs ht p.val u hu
  exact norm_wedge_orthonormal _ _ h1 h2 h3

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanAngularWeight_le (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) : euclideanAngularWeight A J α hs ht p uv ≤ 4 := by
  have hsrc := angularChartCoordinates_source A J α hs ht E p huv
  have hh := norm_sub_le (euclideanLine A J α hs ht p uv.1) (euclideanLine A J α hs ht p uv.2)
  rw [euclideanLine_norm A J α hs ht p uv.1 hsrc.2,euclideanLine_norm A J α hs ht p uv.2 hsrc.1] at hh
  have hsq : ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2 ≤ 4 := by
    nlinarith [norm_nonneg (euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2)]
  exact (mul_le_mul_of_nonneg_left hsq (A.partition.nonneg p uv.2.val.proj)).trans
    (by have h := A.partition.le_one p uv.2.val.proj; nlinarith)

include hE hD in
lemma separating_current_euclidean_angular_moment
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ s : ℝ, 0 < s →
      (∫ uv, euclideanAngularNear A J α hs ht E s p uv ∂μ.prod μ) ≤ F*s^4 := by
  obtain ⟨C,B,L,ρ₀,hC,hB,hL,hρ₀,hpoint⟩ := euclidean_angular_near_point A J α hs ht E hE p
  obtain ⟨ρ₁,K,hρ₁,hK,hang⟩ := separating_current_angular_moment A J α hs ht E hE D hD μ hann
  obtain ⟨M,hM,hmass⟩ := separating_current_euclidean_near_mass A J α hs ht E μ hann p
  let ρ := min ρ₀ (ρ₁/L)
  have hρ : 0 < ρ := lt_min hρ₀ (div_pos hρ₁ hL)
  let F := C*K*L^4+B*M+4/ρ^4
  have hF : 0 ≤ F := by positivity
  refine ⟨F,hF,fun s hs' => ?_⟩
  have hi := euclideanAngularNear_integrable A J α hs ht E s p μ
  by_cases hsρ : s ≤ ρ
  · have hs₀ : s ≤ ρ₀ := hsρ.trans (min_le_left _ _)
    have hs₁ : L*s ≤ ρ₁ := by simpa only [mul_comm] using (le_div_iff₀ hL).mp (hsρ.trans (min_le_right _ _))
    have hA := angularNear_integrable A J α hs ht E hE (L*s) p μ
    have hS : Integrable ((euclideanNearSet A J α hs ht E s p).indicator (fun _ => (1:ℝ))) (μ.prod μ) :=
      (integrable_const _).indicator (euclideanNearSet_closed A J α hs ht E s p).measurableSet
    have hh := integral_mono hi ((hA.const_mul C).add (hS.const_mul (B*s^2))) (hpoint s hs' hs₀)
    simp only [Pi.add_apply] at hh
    rw [integral_add (hA.const_mul C) (hS.const_mul (B*s^2)),integral_const_mul,integral_const_mul] at hh
    have hb₁ := mul_le_mul_of_nonneg_left (hang _ (mul_pos hL hs') hs₁ p) hC
    have hb₂ := mul_le_mul_of_nonneg_left (hmass s hs') (mul_nonneg hB (sq_nonneg s))
    apply hh.trans ((add_le_add hb₁ hb₂).trans ?_)
    dsimp [F]
    have hn : 0 ≤ (4/ρ^4)*s^4 := by positivity
    nlinarith
  · have hpt (uv : UnitPair J α hs ht) : euclideanAngularNear A J α hs ht E s p uv ≤ 4 := by
      by_cases huv : uv ∈ euclideanNearSet A J α hs ht E s p
      · rw [euclideanAngularNear,indicator_of_mem huv]
        exact euclideanAngularWeight_le A J α hs ht E p huv.1
      · rw [euclideanAngularNear,indicator_of_notMem huv]; norm_num
    have hh := integral_mono hi (integrable_const 4) hpt
    rw [integral_const,probReal_univ,one_smul] at hh
    have hpow := pow_le_pow_left₀ hρ.le (le_of_lt (lt_of_not_ge hsρ)) 4
    have hlarge : 4 ≤ (4/ρ^4)*s^4 := by
      rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hρ 4)]
      linarith
    apply hh.trans (hlarge.trans ?_)
    dsimp [F]
    have hn : 0 ≤ (C*K*L^4+B*M)*s^4 := by positivity
    nlinarith
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
