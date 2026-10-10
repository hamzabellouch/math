import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedHeight
import OAI.Probability.Ballisticity.Estimates.WeightedConditioned

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma noDropFinite_lower_rows {d : ℕ} (e : Direction d) (y : Lattice d)
    (hy : signedHeight e y = 0) (J : ℕ) :
    @Measurable _ _ (rowSigma {z | dot (realPosition z) (realPosition (step e)) ≤ (J:ℝ)}) _
      (noDropFinite (realPosition (step e)) y J) := by
  apply (noDropFinite_measurable_ball _ y J).mono (rowSigma_mono ?_) le_rfl
  intro z hz
  change dot (realPosition z) (realPosition (step e)) ≤ (J:ℝ)
  rw [signedHeight_projection]
  have hh := abs_le.mp (hz e.1)
  have hc : signedHeight e z ≤ (J:ℤ) := by
    simp only [signedHeight] at hy ⊢
    cases he : e.2 <;> simp only [he,Bool.false_eq_true,ite_false,ite_true] at hy ⊢ <;> omega
  exact_mod_cast hc

noncomputable def noDropApproxError {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (J : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, noDropFinite ℓ 0 J ω-noDropQuenched ℓ 0 ω ∂environmentLaw ν

lemma noDropApproxError_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (y : Lattice d) (J : ℕ) :
    (∫⁻ ω, noDropFinite ℓ y J ω-noDropQuenched ℓ y ω ∂environmentLaw ν) =
      noDropApproxError ν ℓ J := by
  simp_rw [noDropFinite_translation ℓ _ y J,noDropQuenched_translation ℓ _ y]
  have hh := lintegral_map ((noDropFinite_measurable ℓ 0 J).sub (measurable_noDropQuenched ℓ 0))
    (show Measurable (fun ω : Environment d => fun a => ω (y+a)) by fun_prop)
    (μ := environmentLaw ν)
  rw [environment_translation] at hh
  exact hh.symm

lemma noDropApproxError_le_one {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (J : ℕ) : noDropApproxError ν ℓ J ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂environmentLaw ν :=
      lintegral_mono (fun _ => tsub_le_self.trans prob_le_one)
    _ = 1 := by simp

lemma noDropApproxError_tendsto {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) : Tendsto (noDropApproxError ν ℓ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := environmentLaw ν)
    (f := fun _ => (0 : ℝ≥0∞)) (fun _ => (1 : ℝ≥0∞))
    (fun J => (noDropFinite_measurable ℓ 0 J).sub (measurable_noDropQuenched ℓ 0))
    (fun _ => ae_of_all _ (fun _ => tsub_le_self.trans prob_le_one))
    (by simp) (ae_of_all _ (fun ω => ?_))
  · change Tendsto (fun J => ∫⁻ ω, noDropFinite ℓ 0 J ω-noDropQuenched ℓ 0 ω ∂environmentLaw ν)
      atTop (𝓝 0)
    simpa only [lintegral_zero,Pi.sub_apply] using h
  · have ht := ENNReal.Tendsto.sub (noDropFinite_tendsto ℓ 0 ω)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => noDropQuenched ℓ 0 ω) atTop (𝓝 (noDropQuenched ℓ 0 ω)))
      (Or.inl (measure_ne_top _ _))
    simpa only [Pi.sub_apply,tsub_self] using ht

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma normalizedMeasure_upper_le {Ω : Type*} [MeasurableSpace Ω]
    (μ η : Measure Ω) (hμη : μ ≤ η) (δ c : ℝ≥0∞)
    (hc : c ≤ μ Set.univ) (A : Set Ω) (hA : η A ≤ μ A+δ) :
    normalizedMeasure η A ≤ normalizedMeasure μ A+c⁻¹*δ := by
  change (η Set.univ)⁻¹*η A ≤ (μ Set.univ)⁻¹*μ A+c⁻¹*δ
  calc
    _ ≤ (μ Set.univ)⁻¹*η A := mul_le_mul_left (ENNReal.inv_le_inv.mpr (hμη Set.univ)) _
    _ ≤ (μ Set.univ)⁻¹*(μ A+δ) := mul_le_mul_right hA _
    _ = (μ Set.univ)⁻¹*μ A+(μ Set.univ)⁻¹*δ := mul_add _ _ _
    _ ≤ (μ Set.univ)⁻¹*μ A+c⁻¹*δ :=
      add_le_add le_rfl (mul_le_mul_left (ENNReal.inv_le_inv.mpr hc) δ)

lemma levyProkhorov_normalized_map_le {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ η : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμη : μ ≤ η) (δ c : ℝ≥0∞) (hc : 0 < c) (hδ : δ ≠ ⊤)
    (hcmass : c ≤ μ Set.univ) (hbound : ∀ A, MeasurableSet A → η A ≤ μ A+δ)
    (F : Ω → E) (hF : Measurable F) :
    levyProkhorovDist ((normalizedMeasure η).map F) ((normalizedMeasure μ).map F) ≤ (c⁻¹*δ).toReal := by
  let : IsProbabilityMeasure (normalizedMeasure μ) := normalizedMeasure_probability μ
    (ne_of_gt (hc.trans_le hcmass))
  let : IsProbabilityMeasure (normalizedMeasure η) := normalizedMeasure_probability η
    (ne_of_gt (hc.trans_le (hcmass.trans (hμη Set.univ))))
  let : IsProbabilityMeasure ((normalizedMeasure μ).map F) := inferInstance
  let : IsProbabilityMeasure ((normalizedMeasure η).map F) := inferInstance
  apply levyProkhorovDist_le_of_forall_le _ _ ENNReal.toReal_nonneg
  intro ε B hε hB
  rw [Measure.map_apply hF hB]
  have hb := normalizedMeasure_upper_le μ η hμη δ c hcmass (F ⁻¹' B)
    (hbound _ (hB.preimage hF))
  have he : c⁻¹*δ ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc.ne') hδ)]
    exact ENNReal.ofReal_le_ofReal hε.le
  have hBsub : (normalizedMeasure μ) (F ⁻¹' B) ≤
      ((normalizedMeasure μ).map F) (Metric.thickening ε B) := by
    rw [Measure.map_apply hF Metric.isOpen_thickening.measurableSet]
    exact measure_mono (Set.preimage_mono (Metric.self_subset_thickening (ENNReal.toReal_nonneg.trans_lt hε) B))
  exact hb.trans (add_le_add hBsub he)

lemma weak_limit_of_uniform_approximation {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → ProbabilityMeasure E) (η : ℕ → ℕ → ProbabilityMeasure E)
    (W : ProbabilityMeasure E) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hlim : ∀ J, Tendsto (η J) atTop (𝓝 W))
    (hclose : ∀ J i, levyProkhorovDist (μ i : Measure E) (η J i : Measure E) ≤ δ J) :
    Tendsto μ atTop (𝓝 W) := by
  have hW : Tendsto (fun i => LevyProkhorov.ofMeasure (μ i)) atTop (𝓝 (LevyProkhorov.ofMeasure W)) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨J,hJ⟩ := (hδ.eventually_lt_const (half_pos hε)).exists
    have hη := LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto W |>.comp (hlim J)
    filter_upwards [(Metric.tendsto_nhds.mp hη) (ε/2) (half_pos hε)] with i hi
    exact (dist_triangle _ (LevyProkhorov.ofMeasure (η J i)) _).trans_lt
      (by
        have hc := hclose J i
        dsimp only [Function.comp_apply] at hi
        change dist (LevyProkhorov.ofMeasure (μ i)) (LevyProkhorov.ofMeasure (η J i)) ≤ δ J at hc
        linarith)
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto
    (LevyProkhorov.ofMeasure W) |>.comp hW

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weightedConditioned_apply {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) (hg : Measurable g)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedConditioned ν ℓ g A = (annealedLaw ν (NoDrop ℓ 0))⁻¹ *
      ∫⁻ ω, g ω * quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0) ∂environmentLaw ν := by
  rw [weightedConditioned,Measure.smul_apply,Measure.restrict_apply hA,
    weightedAnnealed_apply ν g hg _ (hA.inter (measurableSet_noDrop ℓ 0))]
  rfl

lemma weightedConditioned_mono {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g h : Environment d → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h)
    (hgh : ∀ ω, g ω ≤ h ω) : weightedConditioned ν ℓ g ≤ weightedConditioned ν ℓ h := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [weightedConditioned_apply ν ℓ g hg A hA,weightedConditioned_apply ν ℓ h hh A hA]
  exact mul_le_mul_right (lintegral_mono (fun ω => mul_le_mul_left (hgh ω) _)) _

lemma weightedConditioned_approx {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g h : Environment d → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h)
    (hgh : ∀ ω, g ω ≤ h ω) (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedConditioned ν ℓ h A ≤ weightedConditioned ν ℓ g A+
      (annealedLaw ν (NoDrop ℓ 0))⁻¹ * ∫⁻ ω, h ω-g ω ∂environmentLaw ν := by
  rw [weightedConditioned_apply ν ℓ g hg A hA,weightedConditioned_apply ν ℓ h hh A hA,← mul_add]
  apply mul_le_mul_right
  have hQ : Measurable (fun ω : Environment d => quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0)) :=
    (Kernel.measurable_coe _ (hA.inter (measurableSet_noDrop ℓ 0))).comp
      (measurable_id.prodMk measurable_const)
  rw [← lintegral_add_left (show Measurable (fun ω => g ω * quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0)) from hg.mul hQ) (fun ω => h ω-g ω)]
  apply lintegral_mono
  intro ω
  calc
    _ = (g ω+(h ω-g ω))*quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0) := by
      rw [add_tsub_cancel_of_le (hgh ω)]
    _ = g ω*quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0)+
        (h ω-g ω)*quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0) := add_mul _ _ _
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' prob_le_one)

lemma weightedConditioned_noDrop_mass {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (y : Lattice d) :
    weightedConditioned ν ℓ (noDropQuenched ℓ y) Set.univ =
      (annealedLaw ν (NoDrop ℓ 0))⁻¹ * sharedNoDropMass ν ℓ 0 y := by
  rw [weightedConditioned_apply ν ℓ _ (measurable_noDropQuenched ℓ y) _ MeasurableSet.univ]
  simp only [Set.univ_inter,sharedNoDropMass,noDropQuenched]
  congr 1
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

lemma weightedConditioned_noDrop_approx {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (y : Lattice d) (J : ℕ) (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedConditioned ν ℓ (noDropFinite ℓ y J) A ≤
      weightedConditioned ν ℓ (noDropQuenched ℓ y) A+
      (annealedLaw ν (NoDrop ℓ 0))⁻¹ * noDropApproxError ν ℓ J := by
  simpa only [noDropApproxError_translation ν ℓ y J] using
    weightedConditioned_approx ν ℓ _ _ (measurable_noDropQuenched ℓ y)
      (noDropFinite_measurable ℓ y J) (fun ω => noDropQuenched_le_finite ℓ y ω J) A hA

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
