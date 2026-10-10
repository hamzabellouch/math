import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePatchContinuity
import OAI.Geometry.TamingCompatibility.Hodge.HodgeNormalDistance

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma gammaNormalWedge_physical_angular (p : A.centers) (N : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
        (normalAngular A J α hs ht E p z u v)^2 ≤
      gammaPatchWedge A J α hs ht E T r p u v +
        (C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,hC,hangular⟩ := gammaNormalWedge_actual_angular A J α hs ht E hE p
  obtain ⟨L,hL,hdist⟩ := normalMap_physical_distance J α hs ht p.val (E p)
  have hLC := (HodgeKernelBounds.leadingConstant_pos (N+2)).le
  refine ⟨L^N*(C*HodgeKernelBounds.leadingConstant (N+2)),by positivity,?_⟩
  intro r hr T z hz u v hu hv
  have hb := hangular N r hr T z hz u v hu hv
  have hd : dist u.val.proj v.val.proj ≤ L*‖z.2‖ := by rw [← hu,← hv]; exact hdist z hz
  have hw := weight_of_dist_bound N (sq_pos_of_pos hr) hL (norm_nonneg z.2) u.val.proj v.val.proj hd
  rw [Real.sqrt_sq hr.le] at hw
  have hdt := physicalCompact_target J α ht A E p ⟨z,hz,rfl⟩
  change (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) ∈
    (extChartAt Model p.val).target ×ˢ (extChartAt Model p.val).target at hdt
  have hp : gammaPatchWedge A J α hs ht E T r p u v =
      unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
        (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
          (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
          (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by
    unfold gammaPatchWedge
    rw [← hv,← hu]
    rw [ManifoldKernelExtension.push_apply p.val _ hdt]
  rw [← hp] at hb
  let a := (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
        (normalAngular A J α hs ht E p z u v)^2
  have hlow : -((C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2)/(1+‖z.2‖/r)^N ≤
      gammaPatchWedge A J α hs ht E T r p u v-a := by rw [neg_div]; dsimp only [a]; linarith only [hb]
  have hh := weighted_negative_lower (by positivity : 0 ≤ (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2)
    (VolterraBounds.weight_pos N (sq_pos_of_pos hr) u.val.proj v.val.proj).le
    (by positivity : 0 < (1+‖z.2‖/r)^N) hw hlow
  have hden : 0 < (1+dist u.val.proj v.val.proj/r)^N := by positivity
  have hew : VolterraBounds.weight N (r^2) u.val.proj v.val.proj =
      (1+dist u.val.proj v.val.proj/r)^N := by
    simp only [VolterraBounds.weight,Real.sqrt_sq hr.le]
  rw [hew] at hh
  have hh' : -(L^N*((C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2))/(1+dist u.val.proj v.val.proj/r)^N ≤
      gammaPatchWedge A J α hs ht E T r p u v-a :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hh)
  change a ≤ _
  have he : -(L^N*((C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2))/
      (1+dist u.val.proj v.val.proj/r)^N =
      -((L^N*(C*HodgeKernelBounds.leadingConstant (N+2)))/r^2)*
        ((1+dist u.val.proj v.val.proj/r)⁻¹)^N := by
    simp only [div_eq_mul_inv,inv_pow]
    ring
  rw [he] at hh'
  linarith only [hh']

include hE in
lemma globalLeadingWedge_physical_angular (N : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ p : A.centers, ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
        (normalAngular A J α hs ht E p z u v)^2 ≤
      unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v +
        (C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N := by
  classical
  dsimp only
  let := geometricMetricSpace J α hs ht
  choose C hC hangular using fun p => gammaNormalWedge_physical_angular A J α hs ht E hE p N
  choose L hL hlow using fun p => gammaPatchWedge_weighted_lower A J α hs ht E hE p N
  refine ⟨(∑ p : A.centers, C p)+(∑ p : A.centers, L p),
    add_nonneg (Finset.sum_nonneg (fun p _ => hC p)) (Finset.sum_nonneg (fun p _ => hL p)),?_⟩
  intro r hr T p z hz u v hu hv
  let b := ((1+dist u.val.proj v.val.proj/r)⁻¹)^N/r^2
  have hb : 0 ≤ b := by positivity
  have hlow' (q : A.centers) : 0 ≤ gammaPatchWedge A J α hs ht E T r q u v+L q*b := by
    have hh := hlow q r hr T u v
    have hew : VolterraBounds.weight N (r^2) u.val.proj v.val.proj =
        (1+dist u.val.proj v.val.proj/r)^N := by
      simp only [VolterraBounds.weight,Real.sqrt_sq hr.le]
    rw [hew] at hh
    have hh' : -L q/r^2/(1+dist u.val.proj v.val.proj/r)^N ≤ gammaPatchWedge A J α hs ht E T r q u v :=
      (div_le_iff₀ (by positivity : 0 < (1+dist u.val.proj v.val.proj/r)^N)).mpr
        (by simpa only [mul_comm,gammaPatchWedge] using hh)
    have he : -L q/r^2/(1+dist u.val.proj v.val.proj/r)^N = -L q*b := by
      dsimp [b]; simp only [div_eq_mul_inv,inv_pow]; ring
    rw [he] at hh'
    linarith only [hh']
  have hsingle := Finset.single_le_sum (s := Finset.univ) (f := fun q =>
    gammaPatchWedge A J α hs ht E T r q u v+L q*b) (fun q _ => hlow' q) (Finset.mem_univ p)
  have hsum : (∑ q : A.centers, gammaPatchWedge A J α hs ht E T r q u v) =
      unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v := by
    unfold unitWedgeKernel
    rw [globalLeading_gamma_sum J α ht A E hr T]
    simp only [sum_apply,map_sum,gammaPatchWedge]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,hsum] at hsingle
  have hcp : C p ≤ ∑ q : A.centers, C q := Finset.single_le_sum (fun q _ => hC q) (Finset.mem_univ p)
  have hh := hangular p r hr T z hz u v hu hv
  have he (a : ℝ) : a/r^2*((1+dist u.val.proj v.val.proj/r)⁻¹)^N = a*b := by dsimp [b]; ring
  rw [he] at hh ⊢
  have hcpm := mul_le_mul_of_nonneg_right hcp hb
  have hlp := mul_nonneg (hL p) hb
  nlinarith only [hh,hsingle,hcpm,hlp]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma gammaWedgeTailKernel_rapid {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
      |C.gammaWedgeTailKernel g T hT.le r u v| ≤ B*r^(2*N) := by
  obtain ⟨M,hM,hb⟩ := C.gammaWedgeTailKernel_uniform g T hT.le
  let B := ((1/120 : ℝ)*HodgeKernelBounds.moment 5 (1/2)*(N.factorial : ℝ)*(2/T)^N)*M^2
  have hB : 0 ≤ B := by
    have hm := (HodgeKernelBounds.moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le
    dsimp [B]
    positivity
  refine ⟨B,hB,fun r hr u v => (hb r u v).trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (HodgeKernelBounds.gammaTail_small_scale N hT hr)
      (by norm_num : (0:ℝ)≤1/120)) (sq_nonneg M)
  exact hh.trans_eq (by dsimp [B]; ring)

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end OAI
