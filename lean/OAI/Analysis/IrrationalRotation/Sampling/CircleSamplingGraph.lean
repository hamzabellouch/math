import OAI.Analysis.IrrationalRotation.Model.CircleSamplingGraph
import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingLp
import OAI.Analysis.IrrationalRotation.Sampling.CircleCharacterDynamics
import OAI.Analysis.IrrationalRotation.Rotation.WeightedGraphMarginals
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

namespace Invariant233.CircleParameterData

theorem measurable_samplingDensity (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (endpoint : Bool) : Measurable (p.samplingDensity θ j n endpoint) := by
  unfold samplingDensity
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_orientedKernel endpoint (p.m j)
    (Int.fract ((n : ℝ) * p.alpha θ i))).comp (p.measurable_coordinate i)

theorem samplingDensity_nonneg (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (endpoint : Bool) (hm : 0 < p.m j) (x : Circle) :
    0 ≤ p.samplingDensity θ j n endpoint x := by
  exact Finset.prod_nonneg fun i _ => (orientedKernel_bounds endpoint hm _ _).1

theorem samplingTranslation_measurable (θ : ℝ) (n : ℕ) :
    Measurable (samplingTranslation θ n) :=
  (continuous_id.add continuous_const).measurable

theorem samplingTranslation_measurePreserving (θ : ℝ) (n : ℕ) :
    MeasurePreserving (samplingTranslation θ n) circleMeasure circleMeasure := by
  change MeasurePreserving (fun x : Circle => x + (((n : ℝ) * θ : ℝ) : Circle))
    volume volume
  exact measurePreserving_add_right volume (((n : ℝ) * θ : ℝ) : Circle)

theorem coordinate_sub_samplingTranslation (p : CircleParameterData) (θ : ℝ)
    (i n : ℕ) (x : Circle) :
    p.coordinate i (x - (((n : ℝ) * θ : ℝ) : Circle)) =
      Int.fract (p.coordinate i x - (n : ℝ) * p.alpha θ i) := by
  have h := CircleCharacterDynamics.character_orbit_representative
    (p.q i : ℤ) (-(n : ℤ)) θ x
  simpa only [coordinate, rep, alpha, neg_zsmul, natCast_zsmul,
    ← AddCircle.coe_nsmul, nsmul_eq_mul, Int.cast_neg, Int.cast_natCast,
    neg_mul, sub_eq_add_neg] using h

theorem kernel_fract_first (m : ℕ) (z v : ℝ) :
    kernel m (Int.fract z) v = kernel m z v := by
  unfold kernel delta
  rw [Int.fract_fract]

theorem fract_sub_fract_right (z v : ℝ) :
    Int.fract (z - Int.fract v) = Int.fract (z - v) := by
  have he : z - Int.fract v = z - v + (⌊v⌋ : ℤ) := by
    rw [Int.fract]
    ring
  rw [he, Int.fract_add_intCast]

theorem samplingDensity_inverse_translation (p : CircleParameterData) (θ : ℝ)
    (j n : ℕ) (x : Circle) :
    p.samplingDensity θ j n false (x - (((n : ℝ) * θ : ℝ) : Circle)) =
      p.samplingDensity θ j n true x := by
  unfold samplingDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [p.coordinate_sub_samplingTranslation]
  simp only [orientedKernel, Bool.false_eq_true, ↓reduceIte, kernel_fract_first]
  unfold kernel delta
  rw [fract_sub_fract_right]

theorem samplingGraph_first_marginal (p : CircleParameterData) (θ : ℝ)
    (j n : ℕ) :
    (p.samplingGraph θ j n).map Prod.fst =
      circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingDensity θ j n false x)) := by
  exact WeightedGraphMarginals.map_fst_graph _ (samplingTranslation_measurable θ n)

theorem samplingGraph_second_marginal (p : CircleParameterData) (θ : ℝ)
    (j n : ℕ) :
    (p.samplingGraph θ j n).map Prod.snd =
      circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingDensity θ j n true x)) := by
  rw [samplingGraph, WeightedGraphMarginals.map_snd_graph _
    (samplingTranslation_measurable θ n)]
  rw [WeightedGraphMarginals.map_withDensity_inverse circleMeasure
    (samplingTranslation_measurePreserving θ n)
    (S := fun x => x - (((n : ℝ) * θ : ℝ) : Circle))
    (continuous_id.sub continuous_const).measurable
    (fun x => by simp [samplingTranslation])
    (p.measurable_samplingDensity θ j n false).ennreal_ofReal]
  congr 1
  funext x
  rw [p.samplingDensity_inverse_translation]

theorem samplingGraphAverage_first_marginal (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 0 < p.m j) :
    (p.samplingGraphAverage θ j r).map Prod.fst =
      circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingAverage θ j r false x)) := by
  rw [samplingGraphAverage, Measure.map_smul _ measurable_fst.aemeasurable,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_fst]
  simp_rw [p.samplingGraph_first_marginal]
  exact (WeightedGraphMarginals.withDensity_real_finset_sum circleMeasure
    (p.samples j r) (fun n => p.samplingDensity θ j n false)
    (fun n _ => p.measurable_samplingDensity θ j n false)
    (fun n _ x => p.samplingDensity_nonneg θ j n false hm x)
    (by positivity : 0 ≤ 1 / ((p.samples j r).card : ℝ))).symm

theorem samplingGraphAverage_second_marginal (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 0 < p.m j) :
    (p.samplingGraphAverage θ j r).map Prod.snd =
      circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingAverage θ j r true x)) := by
  rw [samplingGraphAverage, Measure.map_smul _ measurable_snd.aemeasurable,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_snd]
  simp_rw [p.samplingGraph_second_marginal]
  exact (WeightedGraphMarginals.withDensity_real_finset_sum circleMeasure
    (p.samples j r) (fun n => p.samplingDensity θ j n true)
    (fun n _ => p.measurable_samplingDensity θ j n true)
    (fun n _ x => p.samplingDensity_nonneg θ j n true hm x)
    (by positivity : 0 ≤ 1 / ((p.samples j r).card : ℝ))).symm

theorem samplingGraphAverage_finite (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 0 < p.m j) : IsFiniteMeasure (p.samplingGraphAverage θ j r) := by
  let : IsFiniteMeasure circleMeasure := by unfold circleMeasure; infer_instance
  have hi : Integrable (p.samplingAverage θ j r false) circleMeasure :=
    (p.memLp_samplingAverage θ j r false hm 1).integrable le_rfl
  have hn : 0 ≤ᵐ[circleMeasure] p.samplingAverage θ j r false :=
    Filter.Eventually.of_forall fun x => (p.samplingAverage_bounds θ j r false hm x).1
  have ht := (lintegral_ofReal_ne_top_iff_integrable
    hi.aestronglyMeasurable hn).2 hi
  have : IsFiniteMeasure ((p.samplingGraphAverage θ j r).map Prod.fst) := by
    rw [p.samplingGraphAverage_first_marginal θ j r hm]
    exact isFiniteMeasure_withDensity ht
  exact Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable

theorem samplingGraph_ae_graph (p : CircleParameterData) (θ : ℝ) (j n : ℕ) :
    ∀ᵐ xy ∂p.samplingGraph θ j n, xy.2 = samplingTranslation θ n xy.1 := by
  unfold samplingGraph
  have hg : Measurable (fun x => (x, samplingTranslation θ n x)) :=
    measurable_id.prodMk (samplingTranslation_measurable θ n)
  apply (ae_map_iff hg.aemeasurable ?_).2
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact (isClosed_eq continuous_snd
      (continuous_fst.add continuous_const)).measurableSet

theorem samplingGraph_ae_positive_density (p : CircleParameterData) (θ : ℝ)
    (j n : ℕ) :
    ∀ᵐ xy ∂p.samplingGraph θ j n, 0 < p.samplingDensity θ j n false xy.1 := by
  unfold samplingGraph
  have hg : Measurable (fun x => (x, samplingTranslation θ n x)) :=
    measurable_id.prodMk (samplingTranslation_measurable θ n)
  apply (ae_map_iff hg.aemeasurable
    (measurableSet_lt measurable_const
      ((p.measurable_samplingDensity θ j n false).comp measurable_fst))).2
  apply (ae_withDensity_iff (p.measurable_samplingDensity θ j n false).ennreal_ofReal).2
  exact Filter.Eventually.of_forall fun x hx =>
    ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx)

theorem samplingGraphAverage_ae_graph (p : CircleParameterData) (θ : ℝ) (j r : ℕ) :
    ∀ᵐ xy ∂p.samplingGraphAverage θ j r,
      ∃ n ∈ p.samples j r, xy.2 = samplingTranslation θ n xy.1 := by
  unfold samplingGraphAverage
  apply ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro n hn
  filter_upwards [p.samplingGraph_ae_graph θ j n] with xy hxy
  exact ⟨n, hn, hxy⟩

theorem samplingGraphAverage_ae_positive_density_graph (p : CircleParameterData)
    (θ : ℝ) (j r : ℕ) :
    ∀ᵐ xy ∂p.samplingGraphAverage θ j r,
      ∃ n ∈ p.samples j r, 0 < p.samplingDensity θ j n false xy.1 ∧
        xy.2 = samplingTranslation θ n xy.1 := by
  unfold samplingGraphAverage
  apply ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro n hn
  filter_upwards [p.samplingGraph_ae_graph θ j n,
    p.samplingGraph_ae_positive_density θ j n] with xy hxy hpos
  exact ⟨n, hn, hpos, hxy⟩

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws

open CircleParameterData

theorem samplingAverage_eLpNorm_le_two {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) (hj : 1 ≤ j) (r : ℕ)
    (hr : r < p.q (p.blockEnd (j - 1))) (endpoint : Bool) :
    eLpNorm (p.samplingAverage θ j r endpoint) 2 circleMeasure ≤ 2 := by
  let : IsProbabilityMeasure circleMeasure := by
    constructor
    change volume (Set.univ : Set Circle) = 1
    exact UnitAddCircle.measure_univ
  have he := eLpNorm_add_le
    (f := fun x => p.samplingAverage θ j r endpoint x - 1)
    (g := fun _ : Circle => (1 : ℝ)) (μ := circleMeasure)
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hfun : (fun x => p.samplingAverage θ j r endpoint x - 1) +
      (fun _ : Circle => (1 : ℝ)) = p.samplingAverage θ j r endpoint := by
    funext x
    simp
  rw [hfun] at he
  have hc : eLpNorm (fun _ : Circle => (1 : ℝ)) 2 circleMeasure = 1 := by
    rw [eLpNorm_const' _ (by norm_num) (by norm_num)]
    simp
  rw [hc] at he
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hfrac : ENNReal.ofReal (1 / (j : ℝ)) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hjR
  calc
    _ ≤ eLpNorm (fun x => p.samplingAverage θ j r endpoint x - 1) 2 circleMeasure + 1 := he
    _ ≤ ENNReal.ofReal (1 / (j : ℝ)) + 1 :=
      add_le_add (hp.sampling_L2 j hj r hr endpoint).le le_rfl
    _ ≤ (1 : ENNReal) + 1 := add_le_add hfrac le_rfl
    _ = 2 := by norm_num

theorem samplingGraphAverage_ae_positive_graph {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) (hj : 1 ≤ j) (r : ℕ)
    (hr : r < p.q (p.blockEnd (j - 1))) :
    ∀ᵐ xy ∂p.samplingGraphAverage θ j r,
      ∃ n ∈ p.samples j r, 0 < n ∧ xy.2 = samplingTranslation θ n xy.1 := by
  filter_upwards [p.samplingGraphAverage_ae_graph θ j r] with xy hxy
  obtain ⟨n, hn, he⟩ := hxy
  exact ⟨n, hn, hp.samples_positive j hj r hr n hn, he⟩

end Invariant233.CircleParameterLaws

end

end OAI
