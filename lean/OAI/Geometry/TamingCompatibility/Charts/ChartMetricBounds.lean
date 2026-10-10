import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.GeometricCutoff
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricPairingCLM
import OAI.Geometry.TamingCompatibility.Functional.CompactQuadratic

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldVolume ManifoldHodge
open Set MetricForms MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
local instance {k : ℕ} : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance {k : ℕ} : FiniteDimensional ℝ (MetricForms.Form Space k) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective
local instance {k : ℕ} : NormedAddCommGroup (MetricForms.Form Space k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance {k : ℕ} : NormedSpace ℝ (MetricForms.Form Space k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

include hs hD in

lemma coordinate_metric_bounds (p : A.centers) (k : ℕ)
    (hpair : ContinuousOn (fun x => pairingCLM (coordinateMetric J α ht p.val x) k) (D p).domain) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ coordinateSupport A p, ∀ v : MetricForms.Form Space k,
      ‖v‖^2 ≤ C * (chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v) ∧
      chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v ≤ C * ‖v‖^2 := by
  let Q := fun x => chartDensity J α p.val x • pairingCLM (coordinateMetric J α ht p.val x) k
  have hQ : ContinuousOn Q (coordinateSupport A p) :=
    ((chartDensity_smooth J α hs ht p.val).continuousOn.mono
      ((coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset)).smul
      (hpair.mono (coordinateSupport_domain A J α ht D hD p))
  obtain ⟨C,hC,hbound⟩ := CompactQuadratic.lower_bound (coordinateSupport_compact A p) Q hQ (by
    intro x hx v hv
    exact mul_pos (chartDensity_pos J α ht p.val ((coordinateSupport_domain A J α ht D hD p).trans
      (D p).domain_subset hx)) (lt_of_le_of_ne (pairing_self_nonneg _ _) (Ne.symm (by
        intro h; exact hv ((pairing_self_eq_zero _ _).mp h)))))
  obtain ⟨B,hB⟩ := (coordinateSupport_compact A p).exists_bound_of_continuousOn (f := Q) hQ
  refine ⟨max C (max 1 B),lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  intro x hx v
  have hval : 0 ≤ Q x v v := mul_nonneg (chartDensity_pos J α ht p.val
    ((coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset hx)).le
    (pairing_self_nonneg _ _)
  constructor
  · exact (hbound x hx v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hval)
  · change Q x v v ≤ _
    calc Q x v v ≤ ‖Q x v v‖ := le_abs_self _
         _ ≤ ‖Q x v‖ * ‖v‖ := (Q x v).le_opNorm v
         _ ≤ (‖Q x‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right ((Q x).le_opNorm v) (norm_nonneg _)
         _ ≤ (max C (max 1 B) * ‖v‖) * ‖v‖ := by
           gcongr
           exact (hB x hx).trans ((le_max_right 1 B).trans (le_max_right C (max 1 B)))
         _ = _ := by ring

include hs hD in
lemma coordinate_metric_one_bounds (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ coordinateSupport A p, ∀ v : MetricForms.Form Space 1,
      ‖v‖^2 ≤ C * (chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v) ∧
      chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v ≤ C * ‖v‖^2 :=
  coordinate_metric_bounds A J α hs ht D hD p 1
    (pairingCLM_one_smooth _ (by simp [Space]) (D p).frame (D p).frame_smooth (D p).frame_gram).continuousOn

include hs hD in
lemma coordinate_metric_two_bounds (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ coordinateSupport A p, ∀ v : MetricForms.Form Space 2,
      ‖v‖^2 ≤ C * (chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v) ∧
      chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v ≤ C * ‖v‖^2 :=
  coordinate_metric_bounds A J α hs ht D hD p 2
    (pairingCLM_two_smooth _ (by simp [Space]) (D p).frame (D p).frame_smooth (D p).frame_gram).continuousOn
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_neg_self (g : Metric E) {k : ℕ} (a : Form E k) : pairing g (-a) (-a) = pairing g a a := by
  rw [← neg_one_smul ℝ a,pairing_smul_left,pairing_smul_right]
  ring
end TamingCompatibility.MetricForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume LocalMatrixOperator
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

lemma coordinateIntegrand_self_nonneg {k : ℕ} (p : X) (a : ManifoldForms.Form X k) (z : Space) :
    0 ≤ coordinateIntegrand J α p (GeometricAdjoint.pairing J α ht a a) z := by
  unfold coordinateIntegrand
  by_cases hz : z ∈ (extChartAt Model p).target
  · rw [indicator_of_mem hz]
    exact mul_nonneg (chartDensity_pos J α ht p hz).le (MetricForms.pairing_self_nonneg _ _)
  · rw [indicator_of_notMem hz]

lemma localDelta_pairing (p : A.centers) {a : TwoForm X} (ha : Smooth a)
    (hanti : antiInvariantPart J a = a) {z : Space} (hz : z ∈ (extChartAt Model p.val).target) :
    chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localDelta A J α ht p a z) (localDelta A J α ht p a z) =
    coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
      (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a))) z := by
  rw [localDelta_eq A J α ht p ha hanti hz,MetricForms.pairing_neg_self,
    pairing_chart J α ht p.val (Or.inl rfl) _ _ hz]
  unfold coordinateIntegrand
  rw [indicator_of_mem hz]

variable [CompactSpace X] (hs : IsSmooth α)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include hs hD in
lemma localDelta_norm_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a → antiInvariantPart J a = a → ∀ z,
      ‖oneVector (localDelta A J α ht p a z)‖^2 ≤
        C * coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
          (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a))) z := by
  obtain ⟨C,hC,hbound⟩ := coordinate_metric_one_bounds A J α hs ht D hD p
  refine ⟨(‖oneVector‖^2+1)*C,mul_pos (by positivity) hC,?_⟩
  intro a ha hanti z
  by_cases hz : z ∈ coordinateSupport A p
  · have hh := (hbound z hz (localDelta A J α ht p a z)).1
    have hchart := (coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset hz
    rw [localDelta_pairing A J α ht p ha hanti hchart] at hh
    have ho := pow_le_pow_left₀ (norm_nonneg _) (oneVector.le_opNorm (localDelta A J α ht p a z)) 2
    rw [mul_pow] at ho
    have hi := coordinateIntegrand_self_nonneg J α ht p.val (codifferential J α ht (cutoffForm A p a)) z
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖oneVector‖)
    nlinarith
  · rw [localDelta_zero_off A J α ht p a hz,map_zero,norm_zero,zero_pow (by decide : 2≠0)]
    exact mul_nonneg (mul_nonneg (by positivity) hC.le)
      (coordinateIntegrand_self_nonneg J α ht p.val (codifferential J α ht (cutoffForm A p a)) z)

variable [MeasurableSpace X] [BorelSpace X]
include hs hD in
lemma integral_localDelta_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a → antiInvariantPart J a = a →
      (∫ z, ‖oneVector (localDelta A J α ht p a z)‖^2) ≤
        C * ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
          (codifferential J α ht (cutoffForm A p a)) x ∂geometricVolume A J α := by
  obtain ⟨C,hC,hbound⟩ := localDelta_norm_bound A J α ht hs D hD p
  refine ⟨C,hC,?_⟩
  intro a ha hanti
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => sq_nonneg
    ‖oneVector (localDelta A J α ht p a z)‖))
    ((localDelta_density_integrable A J α ht hs p ha hanti).const_mul C)
    (Filter.Eventually.of_forall (hbound a ha hanti))
  rwa [integral_const_mul,integral_localDelta_density A J α ht hs p ha hanti] at h
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
