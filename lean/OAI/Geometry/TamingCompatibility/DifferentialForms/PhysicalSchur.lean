import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianShellIntegral
import OAI.Geometry.TamingCompatibility.Functional.PhysicalProfile
import OAI.Geometry.TamingCompatibility.Concentration.SchurVanishing

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] in
lemma physicalProfileMass_quadratic
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r →
      physicalProfileMass J α hs ht μ r x ≤ C*r^2 := by
  obtain ⟨C,hC,hbound⟩ := separating_probability_real_shell J α hs ht μ hann
  refine ⟨C,hC,fun x r hr => ?_⟩
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mp (hbound x r hr)

def physicalGradientMass (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (L r : ℝ) (x : X) : ℝ :=
  physicalProfileMass J α hs ht μ (L*r) x/r^3

lemma physicalGradientMass_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    Integrable (physicalGradientMass J α hs ht μ L r) (geometricVolume A J α) :=
  (physicalProfileMass_integrable A J α hs ht μ (mul_pos hL hr)).div_const (r^3)

lemma physicalGradientMass_schur
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) {L : ℝ} (hL : 0 < L) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ r : ℝ, 0 < r →
      (∀ x, r*physicalGradientMass J α hs ht μ L r x ≤ C) ∧
      (∫ x, physicalGradientMass J α hs ht μ L r x ∂geometricVolume A J α) ≤ D*r := by
  obtain ⟨C,hC,hbound⟩ := physicalProfileMass_quadratic J α hs ht μ hann
  obtain ⟨D,hD,hvolume⟩ := physicalProfileMass_volume_growth A J α hs ht μ
  refine ⟨C*L^2,D*L^4,by positivity,by positivity,fun r hr => ⟨?_,?_⟩⟩
  · intro x
    have hh := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hbound x (L*r) (mul_pos hL hr)) (by positivity : 0 ≤ r^3)) hr.le
    have he : r*(C*(L*r)^2/r^3) = C*L^2 := by field_simp
    exact hh.trans_eq he
  · unfold physicalGradientMass
    rw [integral_div]
    calc
      _ ≤ D*(L*r)^4/r^3 := div_le_div_of_nonneg_right (hvolume (L*r) (mul_pos hL hr)) (by positivity)
      _ = _ := by field_simp

lemma physicalGradientMass_L2_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    {V : Type*} [NormedAddCommGroup V] (q : X → V) (hq : MemLp q 2 (geometricVolume A J α))
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun r : ℝ => ∫ x, ‖q x‖*physicalGradientMass J α hs ht μ L r x ∂geometricVolume A J α)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := physicalGradientMass_schur A J α hs ht μ hann hL

  let H := fun r x => if 0 < r then physicalGradientMass J α hs ht μ L r x else 0
  have hi (r : ℝ) (hr : 0 < r) : Integrable (H r) (geometricVolume A J α) := by
    simpa only [H,ite_eq_left hr] using physicalGradientMass_integrable A J α hs ht μ hL hr
  have hn (r : ℝ) (x : X) : 0 ≤ H r x := by
    by_cases hr : 0 < r
    · simp only [H,ite_eq_left hr,physicalGradientMass]
      exact div_nonneg (physicalProfileMass_nonneg J α hs ht μ _ _) (by positivity)
    · simp only [H,ite_eq_right hr,le_refl]
  have hh := integral_norm_mul_tendsto_of_schur q hq H hi hn C D hC hD
    (fun r hr x => by simpa only [H,ite_eq_left hr] using (hbound r hr).1 x)
    (fun r hr => by simpa only [H,ite_eq_left hr] using (hbound r hr).2)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [H,ite_eq_left (show 0 < r from hr)]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable
variable {V : Type*} [NormedAddCommGroup V]

def physicalQError (q : X → V) (L r : ℝ) (x : X) : ℝ :=
  ∫ y, ‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3 ∂geometricVolume A J α

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma physicalQError_nonneg (q : X → V) {L r : ℝ} (hr : 0 < r) (x : X) :
    0 ≤ physicalQError A J α hs ht q L r x := by
  apply integral_nonneg
  intro y
  exact div_nonneg (mul_nonneg (norm_nonneg _) (physicalProfile_nonneg J α hs ht _ _ _)) (by positivity)

omit [SecondCountableTopology X] in
lemma physicalQError_integrand_integrable (q : X → V)
    (hq : Integrable q (geometricVolume A J α)) {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (x : X) :
    Integrable (fun y => ‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3)
      (geometricVolume A J α) := by
  have hm : AEStronglyMeasurable (fun y => physicalProfile J α hs ht (L*r) x y) (geometricVolume A J α) :=
    ((physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply (hq.norm.mul_bdd hm (c := 1) ?_).div_const
  exact Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (physicalProfile_nonneg J α hs ht _ _ _)]
    exact physicalProfile_le_one J α hs ht (mul_pos hL hr) _ _

lemma physicalQError_product_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (q : X → V) (hq : Integrable q (geometricVolume A J α)) {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) :
    Integrable (fun uy : MetricUnit (hermitianMetric J α hs ht) × X =>
      ‖q uy.2‖*physicalProfile J α hs ht (L*r) uy.1.val.proj uy.2/r^3)
        (μ.prod (geometricVolume A J α)) := by
  let := geometricVolume_finite A J α hs ht
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hm : AEStronglyMeasurable (fun uy : MetricUnit (hermitianMetric J α hs ht) × X =>
      physicalProfile J α hs ht (L*r) uy.1.val.proj uy.2) (μ.prod (geometricVolume A J α)) :=
    ((physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp
      ((hp.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
  apply ((hq.norm.comp_snd μ).mul_bdd hm (c := 1) ?_).div_const
  exact Eventually.of_forall fun uy => by
    rw [Real.norm_eq_abs,abs_of_nonneg (physicalProfile_nonneg J α hs ht _ _ _)]
    exact physicalProfile_le_one J α hs ht (mul_pos hL hr) _ _

lemma physicalQError_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (q : X → V) (hq : Integrable q (geometricVolume A J α)) {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) :
    Integrable (fun u : MetricUnit (hermitianMetric J α hs ht) => physicalQError A J α hs ht q L r u.val.proj) μ := by
  let := geometricVolume_finite A J α hs ht
  exact (physicalQError_product_integrable A J α hs ht μ q hq hL hr).integral_prod_left

lemma physicalQError_integral
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (q : X → V) (hq : Integrable q (geometricVolume A J α)) {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) :
    (∫ u, physicalQError A J α hs ht q L r u.val.proj ∂μ) =
      ∫ y, ‖q y‖*physicalGradientMass J α hs ht μ L r y ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  unfold physicalQError
  rw [integral_integral_swap (physicalQError_product_integrable A J α hs ht μ q hq hL hr)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  simp_rw [physicalProfile_symm J α hs ht (L*r) _ y]
  rw [integral_div,integral_const_mul]
  simp only [physicalGradientMass,physicalProfileMass,mul_div_assoc]

lemma physicalQError_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (q : X → V) (hq : MemLp q 2 (geometricVolume A J α)) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun r : ℝ => ∫ u, physicalQError A J α hs ht q L r u.val.proj ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let := geometricVolume_finite A J α hs ht
  apply (physicalGradientMass_L2_limit A J α hs ht μ hann q hq hL).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (physicalQError_integral A J α hs ht μ q (hq.integrable (by norm_num)) hL hr).symm
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
