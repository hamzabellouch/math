import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAngularPhysical

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hE in
lemma same_resolvent_wedge_point_angular (N M : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T C B : ℝ, 0 < T ∧ 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr),
        ∀ p : A.centers, ∀ z ∈ (E p).normalCompact,
        ∀ u v : MetricUnit (hermitianMetric J α hs ht),
        (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
        (extChartAt Model p.val).symm z.1 = v.val.proj →
        (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
          (normalAngular A J α hs ht E p z u v)^2 ≤
          S.wedgeKernel (hermitianMetric J α hs ht) u v +
            (C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N+B*r^(2*M) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,C,hT,hC,_,herror,hker⟩ :=
    same_resolvent_wedge_quantitative A J α hs ht E hE D hD (hermitianMetric J α hs ht) N
  obtain ⟨L,hL,hlead⟩ := globalLeadingWedge_physical_angular A J α hs ht E hE N
  let ρ := Real.sqrt T/2
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.mpr hT) (by norm_num)
  have hρT : 2*ρ^2 ≤ T := by
    have hsqrt := Real.sq_sqrt hT.le
    dsimp [ρ]
    nlinarith
  let R := hodgeSmoothingCover A J α hs ht D hD ρ hρ
  obtain ⟨B,hB,hBR⟩ := R.gammaWedgeTailKernel_rapid (hermitianMetric J α hs ht) hT M
  refine ⟨T,L+C,B,hT,add_nonneg hL hC,hB,fun r hr S p z hz u v hu hv => ?_⟩
  have ha : 0 < 1+dist u.val.proj v.val.proj/r := by positivity
  have hw : VolterraBounds.weight N (r^2) u.val.proj v.val.proj =
      (1+dist u.val.proj v.val.proj/r)^N := by
    simp only [VolterraBounds.weight,Real.sqrt_sq_eq_abs,abs_of_pos hr]
  have hl := hlead r hr T p z hz u v hu hv
  have he := (herror r hr u v).2
  rw [hw] at he
  have he' : -(C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N ≤
      unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v := by
    have habs : |unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤
        (C/r^2)/(1+dist u.val.proj v.val.proj/r)^N :=
      (le_div_iff₀ (pow_pos ha N)).mpr (by simpa only [mul_comm] using he)
    have hb := (neg_le_abs (unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v)).trans habs
    simp only [div_eq_mul_inv,inv_pow] at hb ⊢
    linarith
  have ht' := (neg_le_abs (R.gammaWedgeTailKernel (hermitianMetric J α hs ht) T hT.le r u v)).trans (hBR r hr u v)
  rw [hker r hr S ρ hρ R hρT u v]
  have hd : (L+C)/r^2 = L/r^2+C/r^2 := add_div _ _ _
  rw [hd]
  nlinarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hE in
lemma same_resolvent_wedge_point_lower (N M : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr),
        ∀ u v : MetricUnit (hermitianMetric J α hs ht),
        -(C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N-B*r^(2*M) ≤
          S.wedgeKernel (hermitianMetric J α hs ht) u v := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,C,hT,hC,_,herror,hker⟩ :=
    same_resolvent_wedge_quantitative A J α hs ht E hE D hD (hermitianMetric J α hs ht) N
  obtain ⟨L,hL,hlead⟩ := globalLeadingWedge_weighted_lower A J α hs ht E hE N
  let ρ := Real.sqrt T/2
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.mpr hT) (by norm_num)
  have hρT : 2*ρ^2 ≤ T := by
    have hsqrt := Real.sq_sqrt hT.le
    dsimp [ρ]
    nlinarith
  let R := hodgeSmoothingCover A J α hs ht D hD ρ hρ
  obtain ⟨B,hB,hBR⟩ := R.gammaWedgeTailKernel_rapid (hermitianMetric J α hs ht) hT M
  refine ⟨L+C,B,add_nonneg hL hC,hB,fun r hr S u v => ?_⟩
  have ha : 0 < 1+dist u.val.proj v.val.proj/r := by positivity
  have hw : VolterraBounds.weight N (r^2) u.val.proj v.val.proj =
      (1+dist u.val.proj v.val.proj/r)^N := by
    simp only [VolterraBounds.weight,Real.sqrt_sq_eq_abs,abs_of_pos hr]
  have hl := hlead r hr T u v
  rw [hw] at hl
  have hl' : -(L/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N ≤
      unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v := by
    rw [inv_pow,← div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos ha N)).mpr
    simpa only [neg_div,mul_comm] using hl
  have he := (herror r hr u v).2
  rw [hw] at he
  have he' : -(C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N ≤
      unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v := by
    have habs : |unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤
        (C/r^2)/(1+dist u.val.proj v.val.proj/r)^N :=
      (le_div_iff₀ (pow_pos ha N)).mpr (by simpa only [mul_comm] using he)
    have hb := (neg_le_abs (unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v)).trans habs
    simp only [div_eq_mul_inv,inv_pow] at hb ⊢
    linarith
  have ht' := (neg_le_abs (R.gammaWedgeTailKernel (hermitianMetric J α hs ht) T hT.le r u v)).trans (hBR r hr u v)
  rw [hker r hr S ρ hρ R hρT u v]
  have hd : (L+C)/r^2 = L/r^2+C/r^2 := add_div _ _ _
  rw [hd]
  nlinarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
