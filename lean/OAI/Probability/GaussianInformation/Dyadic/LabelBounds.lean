import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.GaussianTails

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma projection_constant_bound {n k m : ℕ} (hm : 1 < m) (hkn : k ≤ n)
    {B T V : ℝ} (hB : 1 ≤ B) (hT : 1 ≤ T) (hV : 1 ≤ V) {v : ℝ} (hv : 0 ≤ v) (hvV : v ≤ V^k) :
    ((2:ℝ)^(k*(m-1))*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1))^(m-1))^(1/(m:ℝ)) * v^(1-1/(m:ℝ)) ≤
      (4*T*V)^(n+1)*Real.sqrt B := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hV0 : 0 < V := lt_of_lt_of_le (by norm_num) hV
  have hm0 : (0:ℝ) < m := by exact_mod_cast lt_trans Nat.zero_lt_one hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm.le
  have hr : 0 ≤ 1-1/(m:ℝ) := sub_nonneg.mpr ((one_div_le_one_div_of_le (by norm_num) hm1).trans_eq (by norm_num))
  have hTn : 1 ≤ T^n := one_le_pow₀ hT
  have hU : 1 ≤ (B*T^n)^(1/2:ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
  have hbase : 1 ≤ (2:ℝ)^k*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1)) := by
    have hp : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have hp' : 1 ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
    apply one_le_mul_of_one_le_of_one_le hp
    exact le_add_of_nonneg_right (by positivity)
  have he : ((2:ℝ)^(k*(m-1))*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1))^(m-1))^(1/(m:ℝ)) =
      ((2:ℝ)^k*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1)))^(((m-1:ℕ):ℝ)/(m:ℝ)) := by
    rw [pow_mul,← mul_pow,← Real.rpow_natCast_mul (by linarith : 0 ≤ (2:ℝ)^k*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1)))]
    congr 1
    ring
  have hroot := Real.rpow_le_self_of_one_le hbase (show ((m-1:ℕ):ℝ)/(m:ℝ) ≤ 1 by
    rw [div_le_one hm0]
    exact_mod_cast Nat.sub_le m 1)
  have hu : (B*T^n)^(1/2:ℝ) ≤ Real.sqrt B*T^n := by
    rw [Real.mul_rpow hB0.le (pow_nonneg hT0.le _),← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hTn (by norm_num)) (Real.sqrt_nonneg _)
  have hb : (2:ℝ)^k*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1)) ≤ (4:ℝ)^(k+1)*(Real.sqrt B*T^n) := by
    have hp' : 1 ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
    have hu0 : 0 ≤ (B*T^n)^(1/2:ℝ) := Real.rpow_nonneg (mul_nonneg hB0.le (pow_nonneg hT0.le _)) _
    calc
      _ ≤ (2:ℝ)^k*(2*((B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1))) := by gcongr; nlinarith
      _ = (4:ℝ)^(k+1)*(B*T^n)^(1/2:ℝ) := by
        have hp : (4:ℝ)^(k+1) = (2:ℝ)^(k+1)*(2:ℝ)^(k+1) := by rw [← mul_pow]; norm_num
        rw [hp,pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (by positivity)
  have hvb : v^(1-1/(m:ℝ)) ≤ V^k :=
    (Real.rpow_le_rpow hv hvV hr).trans (Real.rpow_le_self_of_one_le (one_le_pow₀ hV) (by have := one_div_nonneg.mpr hm0.le; linarith))
  rw [he]
  calc
    _ ≤ ((4:ℝ)^(k+1)*(Real.sqrt B*T^n))*V^k := mul_le_mul (hroot.trans hb) hvb (Real.rpow_nonneg hv _) (by positivity)
    _ ≤ ((4:ℝ)^(n+1)*(Real.sqrt B*T^(n+1)))*V^(n+1) := by
      have h4 : (4:ℝ)^(k+1) ≤ 4^(n+1) := pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hkn 1)
      have hTpow : T^n ≤ T^(n+1) := pow_le_pow_right₀ hT (Nat.le_succ n)
      have hVpow : V^k ≤ V^(n+1) := pow_le_pow_right₀ hV (by omega)
      exact mul_le_mul (mul_le_mul h4 (mul_le_mul_of_nonneg_left hTpow (Real.sqrt_nonneg B))
        (by positivity) (by positivity)) hVpow (by positivity) (by positivity)
    _ = _ := by rw [mul_pow,mul_pow]; ring

lemma lintegral_weighted_average {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (f : β × α → ℝ) (hf : Measurable f) (hf0 : ∀ q,0 ≤ f q) (hf1 : ∀ q,f q ≤ 1)
    (h : α → ℝ) (hh : Measurable h) :
    (∫⁻ q, ENNReal.ofReal (f q) ∂ν.prod (μ.withDensity (fun x => ENNReal.ofReal |h x|))) =
      ∫⁻ x,ENNReal.ofReal |h x| * ENNReal.ofReal (∫ y,f (y,x) ∂ν) ∂μ := by
  have : SFinite (μ.withDensity (fun x => ENNReal.ofReal |h x|)) := inferInstance
  rw [lintegral_prod_symm _ hf.ennreal_ofReal.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul μ hh.abs.ennreal_ofReal]
  · apply lintegral_congr
    intro x
    change ENNReal.ofReal |h x| * _ = ENNReal.ofReal |h x| * _
    congr 1
    have hi := integrable_bounded_measurable ν (fun y => f (y,x))
      (hf.comp (measurable_id.prodMk measurable_const)) (C := 1) (fun y => by simpa [abs_of_nonneg (hf0 _)] using hf1 (y,x))
    exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun y => hf0 (y,x)))).symm
  · exact hf.ennreal_ofReal.lintegral_prod_left'

lemma actual_good_score_l2bound {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (hm : 1 < m)
    (hdim : m-2+2*(k+1) ≤ n/2) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (g : (Fin k → Fin (n+1) → ℝ) × (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hg0 : ∀ q,0 ≤ g q) (hg1 : ∀ q,g q ≤ 1)
    (hfinite : (∫⁻ q,ENNReal.ofReal (g q) ∂(gaussianRows k (n+1)).prod volume) ≠ ∞) :
    let p := fun z => ∫ X,g (X,projectVector X (normalizedChart Q z)) ∂gaussianRows k (n+1)
    (∫ z,(p z)^2 ∂μ) ≤
      ((weightedProjectionMoment n k m B)^(1/(m:ℝ)) *
        (∫⁻ q, ENNReal.ofReal (g q) ∂(gaussianRows k (n+1)).prod volume)^(1-1/(m:ℝ))).toReal^2 := by
  let f := fun q : (Fin k → Fin (n+1) → ℝ) × Coordinate n =>
    g (q.1,projectVector q.1 (normalizedChart Q q.2))
  have hf : Measurable f := hg.comp (measurable_fst.prodMk (continuous_projectVector.measurable.comp
    (measurable_fst.prodMk ((normalizedChart_measurable Q).comp measurable_snd))))
  let p := fun z => ∫ X,f (X,z) ∂gaussianRows k (n+1)
  have : IsProbabilityMeasure (gaussianRows k (n+1)) := by unfold gaussianRows; infer_instance
  have hp : Measurable p := hf.stronglyMeasurable.integral_prod_left'.measurable
  have hp0 : ∀ z,0 ≤ p z := fun _ => integral_nonneg (fun _ => hg0 _)
  have hp1 : ∀ z,p z ≤ 1 := by
    intro z
    have hi := integrable_bounded_measurable (gaussianRows k (n+1)) (fun X => f (X,z))
      (hf.comp (measurable_id.prodMk measurable_const)) (C := 1)
      (fun _ => by dsimp [f]; rw [abs_of_nonneg (hg0 _)]; exact hg1 _)
    simpa [p] using integral_mono hi (integrable_const (1:ℝ)) (fun X => hg1 (X,projectVector X (normalizedChart Q z)))
  refine l2bound_of_bounded_tests μ p hp hp0 hp1 ?_ ?_
  · apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (weightedProjectionMoment_ne_top _ _ _ _)
    · exact ENNReal.rpow_ne_top_of_nonneg (by
        have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm.le
        exact sub_nonneg.mpr ((one_div_le_one_div_of_le (by norm_num) hm1).trans_eq (by norm_num))) hfinite
  · intro h hh hnorm
    have H := actual_projection_borel_test hn hk hm hdim Q μ hsupport hB hspread h hh hnorm g hg hg0 hg1
    rw [lintegral_weighted_average μ (gaussianRows k (n+1)) f hf (fun _ => hg0 _) (fun _ => hg1 _) h hh] at H
    exact H

noncomputable def goodLabels (k : ℕ) : Set (Fin k → ℝ) := {u | ∑ i,(u i)^2 ≤ (16:ℝ)*k}
lemma measurableSet_goodLabels (k : ℕ) : MeasurableSet (goodLabels k) := by
  unfold goodLabels
  apply measurableSet_le _ measurable_const
  fun_prop

lemma goodLabels_eq_preimage (k : ℕ) : goodLabels k =
    (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (4*Real.sqrt k) := by
  ext u
  simp only [goodLabels,mem_ofPred_eq,mem_preimage,Metric.mem_closedBall,dist_zero_right]
  have he : ‖WithLp.toLp 2 u‖^2 = ∑ i,(u i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  have hs := Real.sq_sqrt (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hn := norm_nonneg (WithLp.toLp 2 u)
  have hp := Real.sqrt_nonneg (k:ℝ)
  constructor <;> intro h <;> nlinarith

lemma volume_goodLabels_ne_top (k : ℕ) : volume (goodLabels k) ≠ ∞ := by
  rw [goodLabels_eq_preimage,(PiLp.volume_preserving_toLp (Fin k)).measure_preimage (Metric.isClosed_closedBall.measurableSet.nullMeasurableSet)]
  exact ne_of_lt (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) _).measure_lt_top

lemma volume_goodLabels_pos {k : ℕ} (hk : 0 < k) : 0 < volume (goodLabels k) := by
  rw [goodLabels_eq_preimage,(PiLp.volume_preserving_toLp (Fin k)).measure_preimage (Metric.isClosed_closedBall.measurableSet.nullMeasurableSet)]
  apply lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin k)) (by positivity : 0 < 4*Real.sqrt (k:ℝ)))
  exact measure_mono Metric.ball_subset_closedBall

noncomputable def labelVolumeConstant : ℝ := 4*Real.exp 1*Real.sqrt Real.pi
lemma labelVolumeConstant_ge_one : 1 ≤ labelVolumeConstant := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hp : 1 ≤ Real.sqrt Real.pi := (Real.le_sqrt (by norm_num) Real.pi_pos.le).mpr (by nlinarith [Real.pi_gt_three])
  unfold labelVolumeConstant
  nlinarith

lemma volume_goodLabels_le {k : ℕ} (hk : 0 < k) :
    volume.real (goodLabels k) ≤ labelVolumeConstant^k := by
  rw [measureReal_def,goodLabels_eq_preimage,
    (PiLp.volume_preserving_toLp (Fin k)).measure_preimage (Metric.isClosed_closedBall.measurableSet.nullMeasurableSet)]
  have h := euclidean_closedBall_volume_le k hk (0 : EuclideanSpace ℝ (Fin k))
    (r := 4*Real.sqrt k) (by positivity)
  have hp : Real.sqrt (k:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hk)).ne'
  change volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (4*Real.sqrt k)) ≤ _
  refine h.trans_eq ?_
  unfold labelVolumeConstant
  congr 1
  field_simp

lemma normalized_label_tail {n k : ℕ} (hn : 0 < n) (Q : Cell n) {z : Coordinate n}
    (hz : z ∈ cellSet Q) :
    gaussianRows k (n+1) {X | projectVector X (normalizedChart Q z) ∉ goodLabels k} ≤
      ENNReal.ofReal (Real.exp (-(k:ℝ)/2)) := by
  simpa only [goodLabels,mem_ofPred_eq,not_le] using gaussianRows_tail (k := k)
    (normalizedChart Q z) (normalizedChart_norm_le hn Q hz)

noncomputable def averagedScores {α β ι : Type*} [MeasurableSpace β]
    (ν : Measure β) (f : β × α → ι → ℝ) (i : ι) (x : α) : ℝ := ∫ y,f (y,x) i ∂ν

lemma measurable_averagedScores {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [SFinite ν] (f : β × α → ι → ℝ) (hf : ∀ i,Measurable (fun q => f q i)) (i : ι) :
    Measurable (averagedScores ν f i) := (hf i).stronglyMeasurable.integral_prod_left'.measurable

lemma integrable_score_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : β × α → ℝ) (hf : Measurable f)
    (hf0 : ∀ q,0 ≤ f q) (hf1 : ∀ q,f q ≤ 1) (x : α) : Integrable (fun y => f (y,x)) ν :=
  integrable_bounded_measurable ν _ (hf.comp (measurable_id.prodMk measurable_const))
    (C := 1) (fun _ => by rw [abs_of_nonneg (hf0 _)]; exact hf1 _)

lemma averagedScores_bounds {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : β × α → ι → ℝ)
    (hf : ∀ i,Measurable (fun q => f q i)) (hf0 : ∀ q i,0 ≤ f q i) (hf1 : ∀ q i,f q i ≤ 1) :
    (∀ i x,0 ≤ averagedScores ν f i x) ∧ (∀ i x,averagedScores ν f i x ≤ 1) := by
  constructor
  · exact fun _ _ => integral_nonneg (fun _ => hf0 _ _)
  · intro i x
    simpa [averagedScores] using
      integral_mono (integrable_score_section ν _ (hf i) (fun _ => hf0 _ _) (fun _ => hf1 _ _) x)
        (integrable_const (1:ℝ)) (fun y => hf1 (y,x) i)

lemma averagedScores_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Fintype ι]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : β × α → ι → ℝ)
    (hf : ∀ i,Measurable (fun q => f q i)) (hf0 : ∀ q i,0 ≤ f q i) (hf1 : ∀ q i,f q i ≤ 1)
    (hfs : ∀ q,∑ i,f q i = 1) (x : α) : ∑ i,averagedScores ν f i x = 1 := by
  unfold averagedScores
  rw [← integral_finsetSum _ (fun i _ => integrable_score_section ν _ (hf i) (fun _ => hf0 _ _) (fun _ => hf1 _ _) x)]
  simp [hfs]

noncomputable def goodRegion (k d : ℕ) : Set ((Fin k → Fin d → ℝ) × (Fin k → ℝ)) :=
  Set.univ ×ˢ goodLabels k
lemma measurableSet_goodRegion (k d : ℕ) : MeasurableSet (goodRegion k d) :=
  MeasurableSet.univ.prod (measurableSet_goodLabels k)

lemma reference_goodRegion_volume (k d : ℕ) :
    (gaussianRows k d).prod volume (goodRegion k d) = volume (goodLabels k) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  simp [goodRegion,Measure.prod_prod]

lemma gaussianRows_probability (k d : ℕ) : IsProbabilityMeasure (gaussianRows k d) := by
  unfold gaussianRows
  infer_instance

lemma finite_reference_scores {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    (ν : Measure β) (S : Set β) (hS : MeasurableSet S) (hSf : ν S ≠ ∞) (hSp : 0 < ν S)
    (g : β → ι → ℝ) (hg : ∀ i,Measurable (fun x => g x i))
    (hg0 : ∀ x i,0 ≤ g x i) (hg1 : ∀ x i,g x i ≤ 1) (hgs : ∀ x,∑ i,g x i = 1) :
    let b := fun i => (∫ x in S,g x i ∂ν)/ν.real S
    (∀ i,0 ≤ b i) ∧ (∑ i,b i = 1) ∧
    (∀ i,(∫⁻ x,ENNReal.ofReal (S.indicator (fun x => g x i) x) ∂ν) = ENNReal.ofReal (ν.real S*b i)) := by
  have : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using lt_top_iff_ne_top.mpr hSf⟩
  have hV : 0 < ν.real S := ENNReal.toReal_pos hSp.ne' hSf
  have hi (i : ι) : Integrable (fun x => g x i) (ν.restrict S) :=
    integrable_bounded_measurable _ _ (hg i) (C := 1) (fun _ => by rw [abs_of_nonneg (hg0 _ _)]; exact hg1 _ _)
  dsimp only
  refine ⟨fun _ => div_nonneg (integral_nonneg (fun _ => hg0 _ _)) hV.le,?_,?_⟩
  · rw [← Finset.sum_div,← integral_finsetSum _ (fun i _ => hi i)]
    simp [hgs,measureReal_restrict_apply MeasurableSet.univ,hV.ne']
  · intro i
    have he : (fun x => ENNReal.ofReal (S.indicator (fun x => g x i) x)) = S.indicator (fun x => ENNReal.ofReal (g x i)) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
    rw [he,lintegral_indicator hS]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ (fun _ => hg0 _ _))]
    congr 1
    field_simp

lemma weightedProjectionMoment_toReal {n k m : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    (weightedProjectionMoment n k m B).toReal =
      (2:ℝ)^(k*(m-1))*(1+(B*tubeConstant^n)^(1/2:ℝ)*(2:ℝ)^(k+1))^(m-1) := by
  unfold weightedProjectionMoment tubeWeightConstant
  rw [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_add (by simp)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_one,ENNReal.toReal_mul,← ENNReal.toReal_rpow]
  simp only [ENNReal.toReal_ofReal (pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) _),
    ENNReal.toReal_ofReal (mul_nonneg hB (pow_nonneg (show 0 ≤ tubeConstant by linarith [tubeConstant_ge_one]) _))]

noncomputable def blockInformationConstant : ℝ := 2*Real.log (4*tubeConstant*labelVolumeConstant)+3
lemma blockInformationConstant_pos : 0 < blockInformationConstant := by
  have hT := tubeConstant_ge_one
  have hV := labelVolumeConstant_ge_one
  have h : 1 ≤ 4*tubeConstant*labelVolumeConstant := by nlinarith
  have := Real.log_nonneg h
  unfold blockInformationConstant
  linarith

end RepeatedLocalization

end OAI
