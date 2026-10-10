import OAI.Probability.PosteriorReplicas.Information.LogComparison
import OAI.Probability.PosteriorReplicas.Kernels.LiftedReplica

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def binMeanBound (k J : ℕ) : ℝ :=
  (volume {y : Labels k | labelNorm y ≤ 1}).toReal * (2+(J:ℝ)*2^k)

lemma label_unitBall_ne_top (k : ℕ) : (volume {y : Labels k | labelNorm y ≤ 1}) ≠ ∞ := by
  rw [label_closedBall_volume]
  exact measure_closedBall_lt_top.ne

lemma label_unitBall_pos (k : ℕ) : 0 < (volume {y : Labels k | labelNorm y ≤ 1}) := by
  rw [label_closedBall_volume]
  exact (measure_ball_pos volume (0 : Vec k) (by norm_num : (0:ℝ)<1)).trans_le
    (measure_mono ball_subset_closedBall)

lemma binMeanBound_pos (k J : ℕ) : 0 < binMeanBound k J := by
  unfold binMeanBound
  exact mul_pos (ENNReal.toReal_pos (label_unitBall_pos k).ne' (label_unitBall_ne_top k)) (by positivity)

lemma binMeanBound_eq (k J : ℕ) : ENNReal.ofReal (binMeanBound k J) =
    volume {y : Labels k | labelNorm y ≤ 1} * (2+(J:ℝ≥0∞)*2^k) := by
  unfold binMeanBound
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (label_unitBall_ne_top k),
    ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_mul (by positivity)]
  simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2)]

lemma normalizedRatio_integrable_mean {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    Integrable (fun z => (normalizedRatio f z).toReal)
      ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) ∧
    (∫ z, (normalizedRatio f z).toReal
      ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) ≤ binMeanBound k J := by
  have hb := normalizedRatio_lintegral_le hd hk hm hkm hf hLt hfL J hcut
  rw [← binMeanBound_eq] at hb
  have ht := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  refine ⟨integrable_toReal_of_lintegral_ne_top (by fun_prop) ht,?_⟩
  rw [integral_toReal (by fun_prop) (ae_lt_top (by fun_prop) ht)]
  exact (ENNReal.toReal_le_toReal ht ENNReal.ofReal_ne_top).mpr hb |>.trans_eq
    (ENNReal.toReal_ofReal (binMeanBound_pos k J).le)

def comparisonEnvelope {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞) (J : ℕ)
    (z : EqualSpace d k m × AuxSpace d ℓ k) : ℝ :=
  Real.log (wishartMoment ℓ m k).toReal + (k:ℝ)*Real.log (projectionGramRatio z) +
    (m:ℝ)*Real.log (gramVolume z.1.1) +
      (m:ℝ)*(Real.log (binMeanBound k J) + (normalizedRatio f z).toReal / binMeanBound k J - 1)

lemma replica_log_comparison_ae {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ) :
    ∀ᵐ z ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k),
      llr ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k))
        ((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)) z -
        observableLog f (observe z) ≤ comparisonEnvelope f J z := by
  have ha := (Measure.quasiMeasurePreserving_fst (ν := auxLaw d ℓ k)).ae (replicaLaw_ae_of_reference (k := k) (m := m) .spherical f
    (ae_equalReference_density_pos hd hk hm .spherical hf hLt hfL))
  have hJ := (Measure.quasiMeasurePreserving_fst (ν := auxLaw d ℓ k)).ae (replicaLaw_ae_of_reference (k := k) (m := m) .spherical f
    (ae_equalReference_affine_pos (by omega) (by omega) .spherical hf hLt hfL))
  have hA := (Measure.quasiMeasurePreserving_fst (ν := auxLaw d ℓ k)).ae (replicaLaw_ae_sensing_full_rank hd hk hm hf hLt hfL)
  filter_upwards [ha,hJ,hA,liftedReplica_llr hd hk hm hf hLt hfL,
    liftedReplica_ae_observable_density_pos hd hk hm hkm hf hLt hfL,
    liftedReplica_ae_projectionGram_pos (by omega) (by omega) (by omega) hf hLt hfL] with z haz hJz hAz hll hz' hJ'
  rw [hll]
  unfold observableLog
  rw [observableLikelihood_observe]
  have hc : 0 < (equalConstant k m).toReal := ENNReal.toReal_pos
    (equalConstant_pos k m).ne' (by unfold equalConstant; exact ENNReal.ofReal_ne_top)
  have hZ : 0 < (wishartMoment ℓ m k).toReal := ENNReal.toReal_pos
    (wishartMoment_pos (by omega : m ≤ ℓ)).ne' (wishartMoment_ne_top hk hkm)
  have hato : 0 < (projectedDensity .spherical f z.1.1 z.1.2.1).toReal :=
    ENNReal.toReal_pos haz.ne' (projectedDensity_ne_top .spherical hLt hfL _ _)
  have ha'to : 0 < (projectedDensity .spherical f (observableRows z.1.2.2 z.2)
      (labels (observableRows z.1.2.2 z.2) (z.1.2.2 0))).toReal :=
    ENNReal.toReal_pos hz'.ne' (projectedDensity_ne_top .spherical hLt hfL _ _)
  have h := log_replica_comparison hc hZ hJz hJ' hato ha'to (gramVolume_pos hAz) (binMeanBound_pos k J) k m
  simpa only [replicaDensity,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hJz.le, ENNReal.toReal_ofReal hJ'.le,
    ENNReal.toReal_ofReal (gramVolume_pos hAz).le,comparisonEnvelope,projectionGramRatio,normalizedRatio] using h

def comparisonCost (d ℓ k m J : ℕ) : ℝ :=
  Real.log (wishartMoment ℓ m k).toReal + (k:ℝ)*((m:ℝ)/2*Real.log ((ℓ:ℝ)+1)) +
    (m:ℝ)*((k:ℝ)/2*Real.log ((d:ℝ)+1)) + (m:ℝ)*Real.log (binMeanBound k J)

lemma comparisonEnvelope_integrable_mean {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    Integrable (@comparisonEnvelope d ℓ k m f J) ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) ∧
      (∫ z, comparisonEnvelope f J z ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) ≤
        comparisonCost d ℓ k m J := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := replicaLaw_probability hd hk hm .spherical hf hLt hfL
  have hu := replicaLaw_ae_tuple_full_rank (k := k) (m := m) (by omega) (by omega) hf hLt hfL
  have hG := projectionGramRatio_log_integrable (k := k) (by omega : m+1≤ℓ) (replicaLaw (k := k) (m := m) .spherical f) hu
  have hA := replicaLaw_sensing_log_integrable (ℓ := ℓ) hd hk hm hf hLt hfL
  obtain ⟨hR,hmR⟩ := normalizedRatio_integrable_mean hd hk hm hkm hf hLt hfL J hcut
  have hterm : Integrable (fun z : EqualSpace d k m × AuxSpace d ℓ k =>
      Real.log (binMeanBound k J) + (normalizedRatio f z).toReal / binMeanBound k J - 1)
      ((replicaLaw .spherical f).prod (auxLaw d ℓ k)) := ((integrable_const (Real.log (binMeanBound k J))).add (hR.div_const (binMeanBound k J))).sub (integrable_const (1:ℝ))
  have hbase : Integrable (fun z : EqualSpace d k m × AuxSpace d ℓ k =>
      Real.log (wishartMoment ℓ m k).toReal + (k:ℝ)*Real.log (projectionGramRatio z) +
        (m:ℝ)*Real.log (gramVolume z.1.1)) ((replicaLaw .spherical f).prod (auxLaw d ℓ k)) := ((integrable_const (Real.log (wishartMoment ℓ m k).toReal)).add
    (hG.const_mul (k:ℝ))).add (hA.const_mul (m:ℝ))
  have hbase2 : Integrable (fun z : EqualSpace d k m × AuxSpace d ℓ k =>
      Real.log (wishartMoment ℓ m k).toReal + (k:ℝ)*Real.log (projectionGramRatio z))
      ((replicaLaw .spherical f).prod (auxLaw d ℓ k)) :=
    (integrable_const _).add (hG.const_mul (k:ℝ))
  have hterm2 : Integrable (fun z : EqualSpace d k m × AuxSpace d ℓ k =>
      Real.log (binMeanBound k J) + (normalizedRatio f z).toReal / binMeanBound k J)
      ((replicaLaw .spherical f).prod (auxLaw d ℓ k)) :=
    (integrable_const _).add (hR.div_const (binMeanBound k J))
  refine ⟨hbase.add (hterm.const_mul (m:ℝ)),?_⟩
  unfold comparisonEnvelope
  rw [integral_add hbase (hterm.const_mul (m:ℝ)), integral_add hbase2 (hA.const_mul (m:ℝ)),
    integral_add (integrable_const (Real.log (wishartMoment ℓ m k).toReal)) (hG.const_mul (k:ℝ)),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub hterm2 (integrable_const (1:ℝ)),
    integral_add (integrable_const (Real.log (binMeanBound k J))) (hR.div_const (binMeanBound k J)),
    integral_div]
  simp only [integral_const,probReal_univ,one_smul]
  have hgm := projectionGramRatio_log_mean_le (k := k) (by omega : m+1≤ℓ) (replicaLaw (k := k) (m := m) .spherical f) hu
  have ham := replicaLaw_sensing_log_mean_le (ℓ := ℓ) hd hk hm hf hLt hfL
  have hrdiv : (∫ z, (normalizedRatio f z).toReal ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) /
      binMeanBound k J ≤ 1 := (div_le_one (binMeanBound_pos k J)).mpr hmR
  unfold comparisonCost
  nlinarith [mul_le_mul_of_nonneg_left hgm (Nat.cast_nonneg (α:=ℝ) k),
    mul_le_mul_of_nonneg_left ham (Nat.cast_nonneg (α:=ℝ) m),
    mul_le_mul_of_nonneg_left hrdiv (Nat.cast_nonneg (α:=ℝ) m)]

lemma replica_lifted_loss {d ℓ k m : ℕ} (hd : 4*k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    (klDiv (replicaLaw (k := k) (m := m) .spherical f) (equalReference ((sphereLaw d).withDensity f))).toReal ≤
      (klDiv (((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map observe)
        (((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)).map observe)).toReal +
      comparisonCost d ℓ k m J := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have hd' : k+m+2 ≤ d := by omega
  have := replicaLaw_probability hd' hk hm .spherical hf hLt hfL
  have hh : klDiv ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k))
      ((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)) ≠ ∞ := by
    rw [klDiv_prod_left]
    exact replica_klDiv_ne_top hd hk hm hf hLt hfL
  obtain ⟨he,heq⟩ := observableLog_normalized (ℓ := ℓ) hd' hk hm hkm hf hLt hfL
  obtain ⟨hF,hFm⟩ := comparisonEnvelope_integrable_mean hd' hk hm hkm hf hLt hfL J hcut
  have hh := entropy_loss_envelope _ _ hh measurable_observe (measurable_observableLog hf)
    he heq.le hF (replica_log_comparison_ae hd' hk hm hkm hf hLt hfL J)
  rw [klDiv_prod_left] at hh
  exact hh.trans (add_le_add le_rfl hFm)

end PosteriorReplicas
end

end OAI
