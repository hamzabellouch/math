import Mathlib
import OAI.Probability.IsingPerceptron.ArrayGeometry
import OAI.Probability.IsingPerceptron.FiniteGaussianVariation
import OAI.Probability.IsingPerceptron.JointShapes

namespace OAI

/-! Cascade Pair. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma prefix_pair_value (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ) :
    prefixPatternMean n 2 b (fun Q => prefixVectorValue n a (Q 0 1)) =
      a 0+∑ d : Fin n, (a (d+1)-a d)*(1-b d) := by
  unfold prefixVectorValue
  rw [prefixPatternMean_add,prefixPatternMean_const,prefixPatternMean_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [prefixPatternMean_mul,prefix_pair_mean_01 n b hb d]

lemma cascade_pair_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ) :
    (∫ σ, cascadeScalarArray n a σ 0 1 ∂cascadeReplicaLaw n b) =
      a 0+∑ d : Fin n, (a (d+1)-a d)*(1-b d) := by
  rw [← prefix_pair_value n b hb a]
  apply integral_congr_ae
  filter_upwards [] with σ
  exact (prefixVectorValue_label n a (σ 0) (σ 1)).symm

lemma integral_depth_telescope {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} {L : Ω → ℕ} (hL : Measurable L) (hLn : ∀ᵐ ω ∂μ, L ω ≤ n) (a : ℕ → ℝ) :
    (∫ ω, a (L ω) ∂μ) = a 0+∑ d : Fin n, (a (d+1)-a d)*μ.real {ω | d.val+1 ≤ L ω} := by
  have hd (d : Fin n) : MeasurableSet {ω | d.val+1 ≤ L ω} :=
    measurableSet_le measurable_const hL
  have hi (d : Fin n) : Integrable (fun ω => (a (d+1)-a d)*(if d.val+1 ≤ L ω then (1:ℝ) else 0)) μ := by
    simpa only [Set.indicator,Set.mem_ofPred_eq] using ((integrable_const (μ := μ) (1:ℝ)).indicator (hd d)).const_mul (a (d+1)-a d)
  calc
    (∫ ω, a (L ω) ∂μ) = ∫ ω, a 0+∑ d : Fin n, (a (d+1)-a d)*(if d.val+1 ≤ L ω then (1:ℝ) else 0) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hLn] with ω hω
      exact (sum_prefix_telescope n (L ω) hω a).symm
    _ = _ := by
      rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun d _ => hi d)),integral_const,
        integral_finsetSum _ (fun d _ => hi d)]
      have he (d : Fin n) : (∫ ω, (if d.val+1 ≤ L ω then (1:ℝ) else 0) ∂μ) = μ.real {ω | d.val+1 ≤ L ω} := by
        refine Eq.trans ?_ (integral_ite_one_eq μ {ω | d.val+1 ≤ L ω} (hd d))
        apply integral_congr_ae
        filter_upwards [] with sample
        by_cases hle : d.val+1 ≤ L sample <;> simp [hle]
      simp only [integral_const_mul,he,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]

 

theorem cascade_pair_law_of_tails {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ)
    {L : Ω → ℕ} (hL : Measurable L) (hLn : ∀ᵐ ω ∂μ, L ω ≤ n)
    (hT : ∀ d : Fin n, μ.real {ω | d.val+1 ≤ L ω} = 1-b d) :
    μ.map (fun ω => a (L ω)) = (cascadeReplicaLaw n b).map (fun σ => cascadeScalarArray n a σ 0 1) := by
  have hAm : Measurable (fun ω => a (L ω)) := (measurable_of_countable a).comp hL
  have hBm : Measurable (fun σ => cascadeScalarArray n a σ 0 1) := by
    exact (measurable_pi_apply 1).comp ((measurable_pi_apply 0).comp (measurable_cascadeScalarArray n a))
  apply Measure.ext
  intro t ht
  rw [Measure.map_apply hAm ht,Measure.map_apply hBm ht]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {ω | a (L ω) ∈ t} = (cascadeReplicaLaw n b).real {σ | cascadeScalarArray n a σ 0 1 ∈ t}
  rw [← integral_ite_one_eq μ {ω | a (L ω) ∈ t} (ht.preimage hAm),
    ← integral_ite_one_eq (cascadeReplicaLaw n b) {σ | cascadeScalarArray n a σ 0 1 ∈ t} (ht.preimage hBm)]
  have h := integral_depth_telescope μ hL hLn (fun k => if a k ∈ t then 1 else 0)
  simp only [hT] at h
  exact h.trans (cascade_pair_integral n b hb (fun k => if a k ∈ t then 1 else 0)).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def uniformCellIndex (n : ℕ) (u : ℝ) : ℕ := min n ⌊((n+1:ℕ):ℝ)*u⌋₊
def uniformExponent (n : ℕ) (d : ℕ) : ℝ := ((d:ℝ)+1)/(n+1:ℕ)

lemma uniformExponent_cascade (n : ℕ) : CascadeExponents n (uniformExponent n) := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  constructor
  · intro i hi
    constructor
    · exact div_pos (by positivity) hn
    · apply (div_lt_one hn).mpr
      exact_mod_cast Nat.succ_lt_succ hi
  · intro i j hij hj
    apply (div_lt_div_iff_of_pos_right hn).mpr
    have hh : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    linarith

lemma measurable_uniformCellIndex (n : ℕ) : Measurable (uniformCellIndex n) := by
  unfold uniformCellIndex
  exact measurable_const.min (Nat.measurable_floor.comp (measurable_id.const_mul _))

lemma uniformCellIndex_le (n : ℕ) (u : ℝ) : uniformCellIndex n u ≤ n := min_le_left _ _

lemma uniformCellIndex_tail_iff (n : ℕ) (d : Fin n) (u : ℝ) :
    d.val+1 ≤ uniformCellIndex n u ↔ uniformExponent n d ≤ u := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  rw [uniformCellIndex,le_min_iff,and_iff_right (by omega : d.val+1 ≤ n),
    Nat.le_floor_iff' (by omega : d.val+1 ≠ 0)]
  simp only [uniformExponent,Nat.cast_add,Nat.cast_one]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < n+1),mul_comm]

lemma unitUniform_Ici_real {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform.real (Ici a) = 1-a := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  have he : unitUniform (Iio a) = ENNReal.ofReal a := by
    rw [measure_congr (Iio_ae_eq_Iic (μ := unitUniform))]
    exact unitUniform_Iic ha
  rw [show Ici a = (Iio a)ᶜ from (compl_Iio).symm,
    measureReal_def,measure_compl measurableSet_Iio (measure_ne_top _ _),measure_univ,he,
    ENNReal.toReal_sub_of_le (by simp [ha.2] : ENNReal.ofReal a ≤ 1) (by simp)]
  simp [ENNReal.toReal_ofReal ha.1]

lemma uniformIndex_tail (n : ℕ) (d : Fin n) :
    unitUniform.real {u | d.val+1 ≤ uniformCellIndex n u} = 1-uniformExponent n d := by
  have h : {u : ℝ | d.val+1 ≤ uniformCellIndex n u} = Ici (uniformExponent n d) := by
    ext u; exact uniformCellIndex_tail_iff n d u
  rw [h]
  exact unitUniform_Ici_real ⟨(uniformExponent_cascade n).1 d d.isLt |>.1.le,
    (uniformExponent_cascade n).1 d d.isLt |>.2.le⟩

lemma cascade_pair_uniformIndex (n : ℕ) (a : ℕ → ℝ) :
    unitUniform.map (fun u => a (uniformCellIndex n u)) =
      (cascadeReplicaLaw n (uniformExponent n)).map (fun σ => cascadeScalarArray n a σ 0 1) :=
  cascade_pair_law_of_tails unitUniform n (uniformExponent n) (uniformExponent_cascade n) a
    (measurable_uniformCellIndex n) (ae_of_all _ (uniformCellIndex_le n)) (uniformIndex_tail n)

lemma uniformCellIndex_eq_floor (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    uniformCellIndex n u = ⌊((n+1:ℕ):ℝ)*u⌋₊ := by
  apply min_eq_right
  have h : ⌊((n+1:ℕ):ℝ)*u⌋₊ < n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) hu.1)]
    exact mul_lt_of_lt_one_right (by positivity) hu.2
  omega

lemma uniformCell_bounds (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    (uniformCellIndex n u:ℝ)/(n+1:ℕ) ≤ u ∧
      u < ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ) := by
  rw [uniformCellIndex_eq_floor n hu]
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using (Nat.floor_le (mul_nonneg (by positivity) hu.1))
  · apply (lt_div_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using Nat.lt_floor_add_one (((n+1:ℕ):ℝ)*u)

lemma uniformCell_left_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => (uniformCellIndex n u:ℝ)/(n+1:ℕ)) atTop (𝓝 u) := by
  have hZ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => u-1/((n:ℝ)+1))
    (h := fun _ : ℕ => u) (by simpa using tendsto_const_nhds.sub hZ) tendsto_const_nhds
  · intro n
    have h := (uniformCell_bounds n hu).2.le
    simp only [Nat.cast_add,Nat.cast_one,add_div] at h ⊢
    linarith
  · exact fun n => (uniformCell_bounds n hu).1

lemma uniformCell_right_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ)) atTop (𝓝 u) := by
  simpa only [add_div,Nat.cast_add,Nat.cast_one,add_zero] using
    (uniformCell_left_tendsto hu).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def uniformCellAverage (q : ℝ → ℝ) (n i : ℕ) : ℝ :=
  ((n+1:ℕ):ℝ)*∫ u in Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)), q u

lemma uniformCell_measure (n i : ℕ) :
    (volume.restrict (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)))).real univ = 1/(n+1:ℕ) := by
  rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioo]
  have he : (((i:ℝ)+1)/(n+1:ℕ))-(i:ℝ)/(n+1:ℕ) = 1/(n+1:ℕ) := by ring
  rw [he,ENNReal.toReal_ofReal (by positivity)]

lemma uniformCell_const (n i : ℕ) (c : ℝ) :
    ((n+1:ℕ):ℝ)*(∫ _ in Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)), c) = c := by
  rw [integral_const,smul_eq_mul,uniformCell_measure]
  field_simp

lemma uniformCell_integrable {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) :
    IntegrableOn q (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ))) := by
  apply Integrable.of_bound hq.measurable.aestronglyMeasurable 1
  exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb u).1] using (hb u).2)

lemma uniformCellAverage_bounds {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) :
    q ((i:ℝ)/(n+1:ℕ)) ≤ uniformCellAverage q n i ∧
      uniformCellAverage q n i ≤ q (((i:ℝ)+1)/(n+1:ℕ)) := by
  have hi := uniformCell_integrable hq hb n i
  have hn : (0:ℝ) ≤ (n+1:ℕ) := by positivity
  constructor
  · rw [← uniformCell_const n i (q ((i:ℝ)/(n+1:ℕ)))]
    apply mul_le_mul_of_nonneg_left _ hn
    apply integral_mono_ae (integrable_const _) hi
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hq hu.1.le
  · rw [← uniformCell_const n i (q (((i:ℝ)+1)/(n+1:ℕ)))]
    apply mul_le_mul_of_nonneg_left _ hn
    apply integral_mono_ae hi (integrable_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hq hu.2.le

lemma uniformCellAverage_mem {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) : uniformCellAverage q n i ∈ Icc (0:ℝ) 1 :=
  ⟨(hb _).1.trans (uniformCellAverage_bounds hq hb n i).1,
    (uniformCellAverage_bounds hq hb n i).2.trans (hb _).2⟩

lemma uniformCellAverage_monotone {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n : ℕ) : Monotone (uniformCellAverage q n) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl|hij
  · rfl
  · apply (uniformCellAverage_bounds hq hb n i).2.trans
    apply le_trans _ (uniformCellAverage_bounds hq hb n j).1
    apply hq
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.succ_le_of_lt hij

lemma uniformCellAverage_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) (hc : ContinuousAt q u) :
    Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (hc.tendsto.comp (uniformCell_left_tendsto hu)) (hc.tendsto.comp (uniformCell_right_tendsto hu))
    (fun n => (uniformCellAverage_bounds hq hb n _).1) (fun n => (uniformCellAverage_bounds hq hb n _).2)

lemma monotone_ae_continuous_unit {q : ℝ → ℝ} (hq : Monotone q) :
    ∀ᵐ u ∂unitUniform, ContinuousAt q u := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  exact (ae_iff).mpr (hq.countable_not_continuousAt.measure_zero unitUniform)

lemma uniformCellAverage_ae_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) :
    ∀ᵐ u ∂unitUniform, Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  filter_upwards [monotone_ae_continuous_unit hq,ae_restrict_mem measurableSet_Ioo] with u hc hu
  exact uniformCellAverage_tendsto hq hb ⟨hu.1.le,hu.2⟩ hc

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_from_delta_sum (v : ℕ → ℝ) (n i : ℕ) (hi : i ≤ n) :
    (∑ j : Fin n, if i ≤ j.val then (v (j.val+1)-v j.val) else 0) = v n-v i := by
  by_cases hz : i=0
  · subst i
    simp only [Nat.zero_le,ite_true,finite_delta_sum]
  · have h := finite_tail_delta_sum v n (i-1) (by omega)
    have he (j : Fin n) : i-1 < j.val ↔ i ≤ j.val := by omega
    simpa only [he,show i-1+1=i by omega] using h

lemma uniformCellAverage_antiderivative {q : ℝ → ℝ} (hq : Monotone q) (n i : ℕ) :
    uniformCellAverage q n i = (n+1:ℕ)*
      ((∫ u in (0:ℝ)..(i+1:ℕ)/(n+1:ℕ), q u)-(∫ u in (0:ℝ)..(i:ℝ)/(n+1:ℕ), q u)) := by
  rw [intervalIntegral.integral_interval_sub_left hq.intervalIntegrable hq.intervalIntegrable]
  have hle : (i:ℝ)/(n+1:ℕ) ≤ (i+1:ℕ)/(n+1:ℕ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.le_succ i
  rw [intervalIntegral.integral_of_le hle,integral_Ioc_eq_integral_Ioo]
  simp only [uniformCellAverage,Nat.cast_add,Nat.cast_one]

lemma uniformCellAverage_tail_sum {q : ℝ → ℝ} (hq : Monotone q) (n j : ℕ) (hj : j ≤ n+1) :
    (∑ i : Fin (n+1), if j ≤ i.val then uniformCellAverage q n i.val else 0) =
      (n+1:ℕ)*(∫ u in Ioo ((j:ℝ)/(n+1:ℕ)) 1, q u) := by
  simp_rw [uniformCellAverage_antiderivative hq n]
  have he (i : Fin (n+1)) :
      (if j ≤ i.val then (n+1:ℕ)*((∫ u in (0:ℝ)..(i.val+1:ℕ)/(n+1:ℕ), q u)-
        (∫ u in (0:ℝ)..(i.val:ℝ)/(n+1:ℕ), q u)) else 0) =
      (n+1:ℕ)*(if j ≤ i.val then (∫ u in (0:ℝ)..(i.val+1:ℕ)/(n+1:ℕ), q u)-
        (∫ u in (0:ℝ)..(i.val:ℝ)/(n+1:ℕ), q u) else 0) := by split <;> simp
  simp_rw [he]
  rw [← Finset.mul_sum,finite_from_delta_sum (fun i => ∫ u in (0:ℝ)..(i:ℝ)/(n+1:ℕ), q u) (n+1) j hj]
  rw [div_self (by positivity : ((n+1:ℕ):ℝ) ≠ 0)]
  rw [intervalIntegral.integral_interval_sub_left hq.intervalIntegrable hq.intervalIntegrable]
  rw [intervalIntegral.integral_of_le ((div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr (by exact_mod_cast hj)),
    integral_Ioc_eq_integral_Ioo]

lemma uniformCellAverage_tail_difference {p q : ℝ → ℝ} (hp : Monotone p) (hq : Monotone q)
    (n j : ℕ) (hj : j ≤ n+1)
    (h : (∫ u in Ioo ((j:ℝ)/(n+1:ℕ)) 1, q u) ≤ ∫ u in Ioo ((j:ℝ)/(n+1:ℕ)) 1, p u) :
    0 ≤ ∑ i : Fin (n+1), if j ≤ i.val then uniformCellAverage p n i.val-uniformCellAverage q n i.val else 0 := by
  have he (i : Fin (n+1)) :
      (if j ≤ i.val then uniformCellAverage p n i.val-uniformCellAverage q n i.val else 0) =
      (if j ≤ i.val then uniformCellAverage p n i.val else 0)-
      (if j ≤ i.val then uniformCellAverage q n i.val else 0) := by split <;> simp
  simp_rw [he]
  rw [Finset.sum_sub_distrib,uniformCellAverage_tail_sum hp n j hj,uniformCellAverage_tail_sum hq n j hj]
  exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left h (by positivity))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def scalarNodeTag (n : ℕ) (v : Option (ForestVertex n)) : ℕ :=
  Encodable.encode ((nodeAddress n v).length,nodeAddress n v,(Unit.unit : Unit))

def scalarGaussianNodes (n : ℕ) (g : ℕ → ℝ) (v : Option (ForestVertex n)) : ℝ :=
  g (scalarNodeTag n v)

lemma scalarNodeTag_injective (n : ℕ) : Function.Injective (scalarNodeTag n) := by
  intro v w h
  exact nodeAddress_injective n (congrArg (fun p => p.2.1) (Encodable.encode_inj.mp h))

lemma scalarGaussianNodes_law (n : ℕ) :
    MeasurePreserving (scalarGaussianNodes n) gaussianCoordinates
      (Measure.infinitePi (fun _ : Option (ForestVertex n) => gaussianReal 0 1)) :=
  gaussian_pullback_measurePreserving (scalarNodeTag n) (scalarNodeTag_injective n)

lemma scalarGaussianRootForest_law (n : ℕ) :
    MeasurePreserving (fun g => ((scalarGaussianNodes n g none),fun v => scalarGaussianNodes n g (some v)))
      gaussianCoordinates ((gaussianReal 0 1).prod
        (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1))) := by
  refine ⟨by unfold scalarGaussianNodes; fun_prop,?_⟩
  change gaussianCoordinates.map ((fun q : Option (ForestVertex n) → ℝ =>
      (q none,fun v => q (some v))) ∘ scalarGaussianNodes n) = _
  rw [← Measure.map_map (by fun_prop) (scalarGaussianNodes_law n).measurable,(scalarGaussianNodes_law n).map_eq]
  have he := infinitePi_option_split (gaussianReal 0 1) (fun _ : ForestVertex n => gaussianReal 0 1)
  have hc : (fun i : Option (ForestVertex n) => i.elim (gaussianReal 0 1) (fun _ => gaussianReal 0 1)) =
      (fun _ => gaussianReal 0 1) := by funext i; cases i <;> rfl
  simpa only [hc] using he

lemma cylinderField_scalar_nodes (n : ℕ) (v : LabeledLeaf n) (q : ℕ → ℝ) (g : ℕ → ℝ) :
    cylinderField (treeFieldCoefficients n v (fun i => pathAmplitude q i) (fun _ : Unit => 1)) g =
      pathAmplitude q 0*scalarGaussianNodes n g none+
        ∑ i : Fin n, pathAmplitude q (i+1)*scalarGaussianNodes n g (some (edgeAt n v i)) := by
  rw [treeFieldCoefficients,cylinderField_feature,Fintype.sum_prod_type]
  simp only [Fintype.sum_unique,mul_one]
  have he (i : Fin (n+1)) : treeFeatureTag n v (i,(Unit.unit : Unit)) = scalarNodeTag n (nodeAt n v i) := by
    unfold treeFeatureTag scalarNodeTag
    rw [nodeAddress_nodeAt_length,nodeAddress_nodeAt]
  simp_rw [he]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,nodeAt_zero,nodeAt_succ,scalarGaussianNodes]

lemma noiseLeafTerminal_additive (n : ℕ) (s : ℕ → ℝ) (F : ℝ → ℝ) (x : ℝ) (v : NoiseLeaf ℝ n) :
    noiseLeafTerminal n (fun _ => F) (fun i p => p.1+s i*p.2) x v =
      F (x+∑ i : Fin n, s i*noiseLeafMark n v i) := by
  induction n generalizing s x with
  | zero => simp [noiseLeafTerminal]
  | succ n ih =>
    rw [noiseLeafTerminal,ih,Fin.sum_univ_succ]
    simp only [noiseLeafMark,Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ]
    congr 1
    ring

lemma noiseLeafTerminal_scalar_nodes (n : ℕ) (ω : LabeledTree n) (q : ℕ → ℝ)
    (F : ℝ → ℝ) (g : ℕ → ℝ) (v : LabeledLeaf n) :
    noiseLeafTerminal n (fun _ => F) (fun i p => p.1+pathAmplitude q (i+1)*p.2)
      (pathAmplitude q 0*scalarGaussianNodes n g none)
      (labeledNoiseLeaf ℝ n (ω,markForestOfCoords ℝ n (fun e => scalarGaussianNodes n g (some e))) v) =
      F (cylinderField (treeFieldCoefficients n v (fun i => pathAmplitude q i) (fun _ : Unit => 1)) g) := by
  rw [noiseLeafTerminal_additive,cylinderField_scalar_nodes]
  simp only [noiseLeafMark_labeled]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma noise_leaf_log_eq_ratio (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (s : S) :
    ∀ᵐ T ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)),
      Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => F) u s v)
        ∂noiseLeafKernel A n T) =
      Real.log ((terminalTreeFactor n b μ u F s T).toReal/(noiseTreeTotal A n T).toReal) := by
  have hfac := noiseTreeFactor_leafIntegral n b hb μ (fun _ => hF) hu s
  have htot : ∀ᵐ T ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)),
      0 < noiseTreeTotal A n T ∧ noiseTreeTotal A n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget A n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  filter_upwards [hfac,htot] with T hfac ht
  simp only [noiseTreeFactor_terminal] at hfac
  rw [hfac,ENNReal.toReal_mul]
  have ht0 : (noiseTreeTotal A n T).toReal ≠ 0 :=
    (ENNReal.toReal_pos ht.1.ne' ht.2.ne).ne'
  rw [mul_div_cancel_left₀ _ ht0]
  congr 1
  exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun v => (Real.exp_pos _).le))
    (((measurable_noiseLeafTerminal n (fun _ => hF) hu).comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)

 

theorem bounded_cascade_leaf_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ} {K : ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (hbound : ∀ s, |F s| ≤ K) (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun T => Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => F) u s v) ∂noiseLeafKernel A n T)
    Integrable L P ∧ (∫ T, L T ∂P) = cascadeRecursion n b μ u F s := by
  have he := noise_leaf_log_eq_ratio n b hb μ hu hF s
  have hi := bounded_noiseCascade_recursion n b hb μ hu hF hbound s
  exact ⟨hi.2.1.congr (Filter.EventuallyEq.symm he),(integral_congr_ae he).trans hi.2.2.1⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma cascadeRecursion_gaussian (n : ℕ) (b s : ℕ → ℝ) (F : ℝ → ℝ)
    (hb : ∀ i < n, b i ≠ 0) :
    cascadeRecursion n b (fun _ => ⟨gaussianReal 0 1,inferInstance⟩)
      (fun i p => p.1+Real.sqrt (s i)*p.2) F =
    (List.ofFn (fun i : Fin n => (s i,b i))).foldr
      (fun sd U => gaussianTransform sd.1 sd.2 U) F := by
  induction n generalizing b s with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    funext x
    change logMean (b 0) (gaussianReal 0 1)
      (fun z => cascadeRecursion n (fun j => b (j+1)) (fun _ => ⟨gaussianReal 0 1,inferInstance⟩)
        (fun i p => p.1+Real.sqrt (s (i+1))*p.2) F (x+Real.sqrt (s 0)*z)) = _
    rw [ih (fun j => b (j+1)) (fun j => s (j+1)) (fun i hi => hb (i+1) (by omega))]
    simp only [Fin.val_zero,Fin.val_succ,gaussianTransform,hb 0 (by omega),ite_false,logMean]

 

theorem bounded_gaussian_cascade_leaf_value (n : ℕ) (b s : ℕ → ℝ)
    (hb : CascadeExponents n b) {F : ℝ → ℝ} {K : ℝ}
    (hF : Measurable F) (hbound : ∀ x, |F x| ≤ K) (x : ℝ) :
    (∫ T, Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => F)
      (fun i p => p.1+Real.sqrt (s i)*p.2) x v) ∂noiseLeafKernel ℝ n T)
      ∂(noiseCascadeLaw ℝ n b (fun _ => ⟨gaussianReal 0 1,inferInstance⟩) : Measure (NoiseTree ℝ n))) =
    (List.ofFn (fun i : Fin n => (s i,b i))).foldr
      (fun sd U => gaussianTransform sd.1 sd.2 U) F x := by
  rw [← cascadeRecursion_gaussian n b s F (fun i hi => (hb.1 i hi).1.ne')]
  exact (bounded_cascade_leaf_recursion n b hb _ (fun i => by fun_prop) hF hbound x).2

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

abbrev PositiveCovariance (m : ℕ) := {S : Matrix (Fin m) (Fin m) ℝ // S.PosSemidef}

def covarianceGaussian (m : ℕ) (S : PositiveCovariance m) : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) :=
  ⟨multivariateGaussian 0 S.1,inferInstance⟩

lemma continuous_covarianceGaussian (m : ℕ) : Continuous (covarianceGaussian m) := by
  let : FirstCountableTopology (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin m → Fin m → ℝ))
  apply continuous_iff_seqContinuous.mpr
  intro S Q hS
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro x
  have hc : Continuous (fun A : PositiveCovariance m =>
      Complex.exp (-(x.ofLp ⬝ᵥ A.1 *ᵥ x.ofLp : ℝ)/2)) := by
    have he (i j : Fin m) : Continuous (fun A : PositiveCovariance m => A.1 i j) := by
      have hc : Continuous (fun A : Matrix (Fin m) (Fin m) ℝ => A i j) :=
        (continuous_apply j).comp (continuous_apply i)
      exact hc.comp continuous_subtype_val
    have hr : Continuous (fun A : PositiveCovariance m => (x.ofLp ⬝ᵥ A.1 *ᵥ x.ofLp : ℝ)) := by
      simp only [dotProduct,Matrix.mulVec]
      exact continuous_finsetSum _ (fun i _ => continuous_const.mul
        (continuous_finsetSum _ (fun j _ => (he i j).mul continuous_const)))
    exact Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp hr).neg).div_const 2)
  have ht := hc.continuousAt.tendsto.comp hS
  simpa only [covarianceGaussian,ProbabilityMeasure.coe_mk,charFun_multivariateGaussian (S _).2,
    charFun_multivariateGaussian Q.2,Function.comp_def,inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub,neg_div] using ht

lemma continuous_gaussianMoment (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Continuous (fun S : PositiveCovariance m =>
      ∫ z : EuclideanSpace ℝ (Fin m), Real.exp (∑ i, f (z i)) ∂multivariateGaussian 0 S.1) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m) => Real.exp (∑ i, f (z i))) := by
    apply Real.continuous_exp.comp
    exact continuous_finsetSum _ (fun i _ => hf.comp (PiLp.continuous_apply _ _ i))
  have hb (z : EuclideanSpace ℝ (Fin m)) : ‖Real.exp (∑ i, f (z i))‖ ≤ Real.exp (m*K) := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ : Fin m, K := Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hK (z i)))
      _ = _ := by simp
  let F := BoundedContinuousFunction.ofNormedAddCommGroup _ hc _ hb
  exact ((ProbabilityMeasure.continuous_iff_forall_continuous_integral).mp
    (continuous_covarianceGaussian m)) F

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace
namespace IsingPerceptron

lemma cylinderCross_comm (a b : ℕ →₀ ℝ) : cylinderCross a b = cylinderCross b a := by
  classical
  let n := a.support.sup id + b.support.sup id + 1
  have ha : ∀ i ∈ a.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  have hb : ∀ i ∈ b.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  rw [cylinderCross_prefix a b ha,cylinderCross_prefix b a hb]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma cylinderCross_fin_covariance {m : ℕ} (A : Fin m → ℕ →₀ ℝ) (x : Fin m → ℝ) :
    (∑ i, x i • A i).sum (fun _ v => v^2) =
      x ⬝ᵥ (fun i j => cylinderCross (A i) (A j)) *ᵥ x := by
  simp only [← cylinderCross_self,cylinderCross_finset_left,cylinderCross_sum_right,cylinderCross_smul,
    Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cylinderCross_comm (A j) (A i)]
  ring

lemma cylinderCross_matrix_posSemidef {m : ℕ} (A : Fin m → ℕ →₀ ℝ) :
    Matrix.PosSemidef (fun i j => cylinderCross (A i) (A j)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change cylinderCross (A j) (A i) = cylinderCross (A i) (A j)
    exact cylinderCross_comm _ _
  · intro x
    simp only [star_trivial]
    rw [← cylinderCross_fin_covariance]
    exact Finsupp.sum_nonneg (fun _ _ => sq_nonneg _)

lemma cylinder_vector_law {m : ℕ} (A : Fin m → ℕ →₀ ℝ) :
    gaussianCoordinates.map (fun g => (WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m))) =
      multivariateGaussian 0 (fun i j => cylinderCross (A i) (A j)) := by
  have hM : Measurable (fun g => (WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m))) :=
    (by fun_prop : Measurable (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))).comp
      (Measurable.of_eval (fun i => measurable_cylinderField (A i)))
  let S : Matrix (Fin m) (Fin m) ℝ := fun i j => cylinderCross (A i) (A j)
  change gaussianCoordinates.map (fun g => (WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m))) = multivariateGaussian 0 S
  have : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) := inferInstance
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_apply, integral_map hM.aemeasurable (by fun_prop)]
  have he (g : ℕ → ℝ) :
      ⟪(WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m)),x⟫_ℝ =
        cylinderField (∑ i, x i • A i) g := by
    rw [cylinderField_finset_sum]
    simp only [PiLp.inner_apply,cylinderField_smul,Real.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp_rw [he]
  rw [← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun z : ℝ => Complex.exp ((z:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    cylinderField_law]
  have hc : (∫ y : ℝ, Complex.exp ((y : ℂ) * Complex.I)
      ∂gaussianReal 0 ((∑ i, x i • A i).sum (fun _ v => v^2)).toNNReal) =
      charFun (gaussianReal 0 ((∑ i, x i • A i).sum (fun _ v => v^2)).toNNReal) 1 := by
    rw [charFun_apply]
    simp only [Real.inner_apply,mul_one]
  rw [hc]
  rw [charFun_gaussianReal,charFun_multivariateGaussian (show S.PosSemidef from cylinderCross_matrix_posSemidef A)]
  have hn : 0 ≤ (∑ i, x i • A i).sum (fun _ v => v^2) :=
    Finsupp.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : (↑((∑ i, x i • A i).sum (fun _ v => v^2)).toNNReal : ℝ) =
      x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
    rw [Real.coe_toNNReal _ hn]
    exact cylinderCross_fin_covariance A x.ofLp
  simp only [Complex.ofReal_zero,Complex.ofReal_one,mul_zero,zero_mul,zero_sub,one_pow,mul_one,inner_zero_right,hv]

end IsingPerceptron

end

end OAI
