import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedHeightSub
import OAI.Probability.Ballisticity.Walk.VaryingHeightPathGaussianEval

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

lemma gaussian_abs_tail (v : ℝ≥0) (hv : 0 < (v : ℝ)) (a : ℝ) (ha : 0 ≤ a) :
    (gaussianReal 0 v).real {z | a ≤ |z|} ≤ 2*Real.exp (-a^2/(2*v)) := by
  have hu := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) a
    (div_nonneg ha hv.le) (integrable_exp_mul_gaussianReal (a/v))
  have hl := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) (-a)
    (neg_nonpos.mpr (div_nonneg ha hv.le)) (integrable_exp_mul_gaussianReal (-(a/v)))
  rw [mgf_id_gaussianReal] at hu hl
  simp only [zero_mul,zero_add,← Real.exp_add] at hu hl
  have he1 : -(a/(v:ℝ))*a+v*(a/v)^2/2 = -a^2/(2*v) := by field_simp; ring
  have he2 : -(-(a/(v:ℝ)))*(-a)+v*(-(a/v))^2/2 = -a^2/(2*v) := by field_simp; ring
  rw [he1] at hu
  rw [he2] at hl
  have he : {z : ℝ | a ≤ |z|} = {z : ℝ | a ≤ z} ∪ {z : ℝ | z ≤ -a} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_union,le_abs]
    exact or_congr Iff.rfl (by constructor <;> intro h <;> linarith)
  rw [he]
  exact (measureReal_union_le _ _).trans (by simpa only [id_eq,two_mul] using add_le_add hu hl)

lemma distribution_closed_limsup {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (F : ℕ → Ω → ℝ)
    (hF : ∀ i, Measurable (F i)) (η : Measure ℝ) [IsProbabilityMeasure η]
    (hlim : TendstoInDistribution F atTop id μ η) (A : Set ℝ) (hA : IsClosed A) :
    limsup (fun i => μ i (F i ⁻¹' A)) atTop ≤ η A := by
  let P : ℕ → ProbabilityMeasure ℝ := fun i => ⟨(μ i).map (F i),
    (Measure.isProbabilityMeasure_map_iff (hF i).aemeasurable).mpr inferInstance⟩
  have hp : Tendsto P atTop (𝓝 (⟨η,inferInstance⟩ : ProbabilityMeasure ℝ)) := by
    simpa only [Measure.map_id] using hlim.tendsto
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hp hA
  change limsup (fun i => ((μ i).map (F i)) A) atTop ≤ η A at hh
  simpa only [Measure.map_apply (hF _) hA.measurableSet] using hh

lemma distribution_abs_limsup {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (F : ℕ → Ω → ℝ)
    (hF : ∀ i, Measurable (F i)) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (hlim : TendstoInDistribution F atTop id μ (gaussianReal 0 v)) (a : ℝ) (ha : 0 ≤ a) :
    limsup (fun i => (μ i).real {ω | a ≤ |F i ω|}) atTop ≤ 2*Real.exp (-a^2/(2*v)) := by
  have hh := distribution_closed_limsup μ F hF (gaussianReal 0 v) hlim {z | a ≤ |z|}
    (isClosed_le continuous_const continuous_abs)
  have he : limsup (fun i => (μ i).real {ω | a ≤ |F i ω|}) atTop =
      (limsup (fun i => μ i {ω | a ≤ |F i ω|}) atTop).toReal := by
    exact ENNReal.limsup_toReal_eq (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      (Eventually.of_forall fun i => prob_le_one)
  rw [he]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hh).trans (gaussian_abs_tail v hv a ha)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma recordFluctuationScale_pos {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) {r : ℝ} (hr : 0 < r) :
    0 < fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ hp
  exact div_pos (sq_pos_of_pos hr) (truncatedVariance_pos _ _ (measurable_commonIncrementProcess ℓ f 0)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans) hr)

noncomputable def scaledRecordEndpoint {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (k : ℕ) (x : Lattice d) (X : Path d) : ℝ :=
  (signedCoordinate f (recordIndexPosition ℓ k (fun j => X j-x))-(k:ℝ)*θ)/r

lemma measurable_scaledRecordEndpoint {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (k : ℕ) (x : Lattice d) : Measurable (scaledRecordEndpoint ℓ f θ r k x) := by
  unfold scaledRecordEndpoint
  exact ((((measurable_of_countable (signedCoordinate f)).comp
    (measurable_recordIndexPosition ℓ k)).comp (by fun_prop)).sub_const _).div_const _

theorem shared_endpoint_limits {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    {t : ℝ} (ht : 0 < t) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    letI : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
      sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
        (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
    TendstoInDistribution (fun i Z => scaledRecordEndpoint ℓ f (θ i) (r i) ⌊t*n i⌋₊ (x i) Z.1)
      atTop id (fun i => sharedConditionedPairLaw ν ℓ (x i) (y i))
      (gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ)))) ∧
    TendstoInDistribution (fun i Z => scaledRecordEndpoint ℓ f (θ i) (r i) ⌊t*n i⌋₊ (y i) Z.2)
      atTop id (fun i => sharedConditionedPairLaw ν ℓ (x i) (y i))
      (gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ)))) := by
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
  have hnpos : ∀ i, 0 < n i := fun i => recordFluctuationScale_pos ν hue e f hef htrans (hrpos i)
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  obtain ⟨W,hW,hlim⟩ := shared_path_marginal_limits ν hue e f hef htrans r hr ht.le
  have hW' : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (t*(1/(2*commonMeanWidth ν ℓ))) I := by
    intro I
    simpa only [div_eq_mul_inv,one_mul] using hW I
  have hk : ∀ i, (⌊t*n i⌋₊ : ℝ) ≤ t*n i := fun i => Nat.floor_le (mul_pos ht (hnpos i)).le
  have hkn : Tendsto (fun i => (⌊t*n i⌋₊ : ℝ)/n i) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht.le).comp hn
  refine ⟨?_,?_⟩
  · have hh := varying_height_path_gaussian_eval μ
      (fun i h Z => signedCoordinate f (recordIndexPosition ℓ h (fun j => Z.1 j-x i))-(h:ℝ)*θ i)
      (fun i h => (((measurable_of_countable (signedCoordinate f)).comp
        (measurable_recordIndexPosition ℓ h)).comp (by fun_prop)).sub_const _)
      r n hnpos t ht (1/(2*commonMeanWidth ν ℓ)) W (hlim x y hxy).1 hW' _ hk hkn
    simpa only [scaledRecordEndpoint,div_eq_mul_inv,one_mul,mul_comm ((2*commonMeanWidth ν ℓ)⁻¹)] using hh
  · have hh := varying_height_path_gaussian_eval μ
      (fun i h Z => signedCoordinate f (recordIndexPosition ℓ h (fun j => Z.2 j-y i))-(h:ℝ)*θ i)
      (fun i h => (((measurable_of_countable (signedCoordinate f)).comp
        (measurable_recordIndexPosition ℓ h)).comp (by fun_prop)).sub_const _)
      r n hnpos t ht (1/(2*commonMeanWidth ν ℓ)) W (hlim x y hxy).2 hW' _ hk hkn
    simpa only [scaledRecordEndpoint,div_eq_mul_inv,one_mul,mul_comm ((2*commonMeanWidth ν ℓ)⁻¹)] using hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
