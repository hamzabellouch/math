import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.LabelBounds

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
lemma normalized_block_information {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (hm : 1 < m)
    (hdim : m-2+2*(k+1) ≤ n/2) (hkn : k ≤ n) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 1 ≤ B) (hspread : DyadicSpread μ Q B)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : (Fin k → Fin (n+1) → ℝ) × (Fin k → ℝ) → ι → ℝ)
    (hg : ∀ i,Measurable (fun q => g q i)) (hg0 : ∀ q i,0 ≤ g q i)
    (hgs : ∀ q,∑ i,g q i = 1) :
    finiteInformation μ (fun i z => ∫ X,g (X,projectVector X (normalizedChart Q z)) i ∂gaussianRows k (n+1)) ≤
      blockInformationConstant*(n+1)+Real.log B+
        (2/(m:ℝ)+Real.exp (-(k:ℝ)/2))*Real.log (Fintype.card ι) := by
  classical
  let ν := gaussianRows k (n+1)
  let S := goodRegion k (n+1)
  have hS : MeasurableSet S := measurableSet_goodRegion _ _
  have : IsProbabilityMeasure ν := gaussianRows_probability _ _
  have hg1 : ∀ q i,g q i ≤ 1 := by
    intro q i
    rw [← hgs q]
    exact Finset.single_le_sum (fun j _ => hg0 q j) (Finset.mem_univ i)
  let a := fun q : (Fin k → Fin (n+1) → ℝ) × Coordinate n => (q.1,projectVector q.1 (normalizedChart Q q.2))
  have ha : Measurable a := measurable_fst.prodMk (continuous_projectVector.measurable.comp
    (measurable_fst.prodMk ((normalizedChart_measurable Q).comp measurable_snd)))
  let gp := fun q i => S.indicator (fun q => g q i) q
  let gq := fun q i => Sᶜ.indicator (fun q => g q i) q
  have hgp : ∀ i,Measurable (fun q => gp q i) := fun i => (hg i).indicator hS
  have hgq : ∀ i,Measurable (fun q => gq q i) := fun i => (hg i).indicator hS.compl
  have hgp0 : ∀ q i,0 ≤ gp q i := fun q _ => Set.indicator_nonneg (fun _ _ => hg0 _ _) q
  have hgq0 : ∀ q i,0 ≤ gq q i := fun q _ => Set.indicator_nonneg (fun _ _ => hg0 _ _) q
  have hgp1 : ∀ q i,gp q i ≤ 1 := by intro q i; by_cases h : q ∈ S <;> simp [gp,h,hg1]
  have hgq1 : ∀ q i,gq q i ≤ 1 := by intro q i; by_cases h : q ∈ S <;> simp [gq,h,hg1]
  let p := averagedScores ν (fun q i => gp (a q) i)
  let q := averagedScores ν (fun q i => gq (a q) i)
  have hp : ∀ i,Measurable (p i) := measurable_averagedScores _ _ (fun i => (hgp i).comp ha)
  have hq : ∀ i,Measurable (q i) := measurable_averagedScores _ _ (fun i => (hgq i).comp ha)
  have hpb := averagedScores_bounds ν (fun q i => gp (a q) i) (fun i => (hgp i).comp ha) (fun _ _ => hgp0 _ _) (fun _ _ => hgp1 _ _)
  have hqb := averagedScores_bounds ν (fun q i => gq (a q) i) (fun i => (hgq i).comp ha) (fun _ _ => hgq0 _ _) (fun _ _ => hgq1 _ _)
  have hpq : ∀ i z,p i z+q i z = ∫ X,g (X,projectVector X (normalizedChart Q z)) i ∂ν := by
    intro i z
    dsimp only [p,q,averagedScores]
    rw [← integral_add]
    rotate_left
    · exact integrable_score_section ν _ ((hgp i).comp ha) (fun _ => hgp0 _ _) (fun _ => hgp1 _ _) z
    · exact integrable_score_section ν _ ((hgq i).comp ha) (fun _ => hgq0 _ _) (fun _ => hgq1 _ _) z
    apply integral_congr_ae
    filter_upwards [] with X
    have he : gp (a (X,z)) i+gq (a (X,z)) i = g (a (X,z)) i := by
      by_cases h : a (X,z) ∈ S <;> simp [gp,gq,h]
    exact he
  have hpqs : ∀ z,∑ i,(p i z+q i z) = 1 := by
    intro z
    simp_rw [hpq]
    exact averagedScores_sum ν (fun q i => g (a q) i) (fun i => (hg i).comp ha) (fun _ _ => hg0 _ _) (fun _ _ => hg1 _ _) (fun _ => hgs _) z
  have hvol : ν.prod volume S = volume (goodLabels k) := reference_goodRegion_volume _ _
  let v := (ν.prod volume).real S
  have hvp : 0 < v := ENNReal.toReal_pos (by rw [hvol]; exact (volume_goodLabels_pos hk).ne') (by rw [hvol]; exact volume_goodLabels_ne_top _)
  let b := fun i => (∫ q in S,g q i ∂ν.prod volume)/v
  obtain ⟨hb0,hbs,hbi⟩ := finite_reference_scores (ν.prod volume) S hS
    (by rw [hvol]; exact volume_goodLabels_ne_top _) (by rw [hvol]; exact volume_goodLabels_pos hk) g hg hg0 hg1 hgs
  change (∀ i,0 ≤ b i) at hb0
  change (∑ i,b i = 1) at hbs
  change ∀ i,(∫⁻ q,ENNReal.ofReal (gp q i) ∂ν.prod volume) = ENNReal.ofReal (v*b i) at hbi
  let A := (4*tubeConstant*labelVolumeConstant)^(n+1)*Real.sqrt B
  let r : ℝ := 1-1/(m:ℝ)
  have hm0 : (0:ℝ) < m := by exact_mod_cast lt_trans Nat.zero_lt_one hm
  have hm1 : (1:ℝ) < m := by exact_mod_cast hm
  have hr : 0 < r := by dsimp [r]; rw [sub_pos]; exact (div_lt_one hm0).mpr hm1
  have hr1 : r ≤ 1 := by dsimp [r]; have := one_div_nonneg.mpr hm0.le; linarith
  have hbase : 1 ≤ 4*tubeConstant*labelVolumeConstant := by nlinarith [tubeConstant_ge_one,labelVolumeConstant_ge_one]
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hbase) ((Real.le_sqrt (by norm_num) (by linarith : 0 ≤ B)).mpr (by simpa using hB))
  have hbound : ∀ i,(∫ z,(p i z)^2 ∂μ) ≤ (A*(b i)^r)^2 := by
    intro i
    have H := actual_good_score_l2bound hn hk hm hdim Q μ hsupport (by linarith : 0 ≤ B) hspread
      (fun q => gp q i) (hgp i) (fun _ => hgp0 _ _) (fun _ => hgp1 _ _) (by rw [hbi i]; exact ENNReal.ofReal_ne_top)
    apply H.trans
    apply pow_le_pow_left₀ ENNReal.toReal_nonneg
    rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,hbi i,← ENNReal.toReal_rpow,ENNReal.toReal_ofReal (mul_nonneg hvp.le (hb0 i)),weightedProjectionMoment_toReal (by linarith)]
    rw [Real.mul_rpow hvp.le (hb0 i),← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hb0 i) _)
    exact projection_constant_bound hm hkn hB tubeConstant_ge_one labelVolumeConstant_ge_one hvp.le
      (by simpa only [v,measureReal_def,hvol] using volume_goodLabels_le hk)
  have hbad : ∑ i,scoreMass μ (q i) ≤ Real.exp (-(k:ℝ)/2) := by
    have hqi (i : ι) : Integrable (q i) μ := integrable_bounded_measurable μ _ (hq i) (C := 1)
      (fun z => by rw [abs_of_nonneg (hqb.1 i z)]; exact hqb.2 i z)
    unfold scoreMass
    rw [← integral_finsetSum _ (fun i _ => hqi i)]
    apply le_trans (integral_mono_ae (integrable_finsetSum _ (fun i _ => hqi i)) (integrable_const (Real.exp (-(k:ℝ)/2))) ?_) (by simp)
    have hsupp : ∀ᵐ z ∂μ,z ∈ cellSet Q := ae_iff.mpr hsupport
    filter_upwards [hsupp] with z hz
    change ∑ i,(∫ X,gq (a (X,z)) i ∂ν) ≤ Real.exp (-(k:ℝ)/2)
    rw [← integral_finsetSum]
    rotate_left
    · intro i _
      exact integrable_score_section ν _ ((hgq i).comp ha) (fun _ => hgq0 _ _) (fun _ => hgq1 _ _) z
    have he : (fun X => ∑ i,gq (a (X,z)) i) = {X | projectVector X (normalizedChart Q z) ∉ goodLabels k}.indicator (fun _ => (1:ℝ)) := by
      funext X
      by_cases h : projectVector X (normalizedChart Q z) ∈ goodLabels k
      · simp [gq,a,S,goodRegion,h]
      · simp [gq,a,S,goodRegion,h,hgs]
    rw [he,integral_indicator]
    · simp only [integral_const,smul_eq_mul,mul_one]
      apply ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
      simpa only [Measure.restrict_apply_univ] using (normalized_label_tail (k := k) hn Q hz)
    · exact ((measurableSet_goodLabels k).preimage (continuous_projectVector.measurable.comp (measurable_id.prodMk measurable_const))).compl
  have H := finiteInformation_good_bad_bound μ p q hp hq hpb.1 hqb.1 hpqs b hb0 hbs hA hr hr1 hbound hbad
  have hlogA : 2*Real.log A = 2*(n+1)*Real.log (4*tubeConstant*labelVolumeConstant)+Real.log B := by
    rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr (by linarith)).ne',Real.log_pow,Real.log_sqrt (by linarith)]
    push_cast
    ring
  simp_rw [hpq] at H
  rw [hlogA] at H
  dsimp only [r] at H
  dsimp only [ν] at H
  have he : 2-2*(1-1/(m:ℝ)) = 2/(m:ℝ) := by ring
  rw [he] at H
  unfold blockInformationConstant
  have hnn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

lemma exactLabel_normalization {n : ℕ} (Q : Cell n) (X : GaussianBlock n) (z : Coordinate n) :
    (fun r => (2:ℝ)^(- (Q.1:ℤ))*projectVector X (normalizedChart Q z) r+exactLabel X (cellCenter Q) r) =
      exactLabel X z := by
  funext r
  have hp : ((2:ℝ)^Q.1) ≠ 0 := by positivity
  simp only [projectVector,normalizedChart,PiLp.smul_apply,smul_eq_mul,PiLp.sub_apply,eChart,exactLabel]
  have he : ∑ j,X r j*((2:ℝ)^Q.1*(chart z j-chart (cellCenter Q) j)) =
      (2:ℝ)^Q.1*((∑ j,X r j*chart z j)-(∑ j,X r j*chart (cellCenter Q) j)) := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  simp only [_root_.zpow_neg,zpow_natCast]
  field_simp
  ring

lemma actual_block_information {n N : ℕ} (hn : 32 ≤ n) (hN : 1 ≤ N)
    (Q : Cell n) (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 1 ≤ B) (hspread : DyadicSpread μ Q B)
    (rule : BlockRule n N) :
    finiteInformation μ (fun w z => blockProbability rule z w) ≤
      blockInformationConstant*(n+1)+Real.log B+
        (2/(n/8:ℕ)+Real.exp (-(n/16:ℕ)/2))*Real.log N := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0,by omega⟩⟩
  let a : GaussianBlock n × Label n → GaussianBlock n × Label n :=
    fun q => (q.1,fun r => (2:ℝ)^(- (Q.1:ℤ))*q.2 r+exactLabel q.1 (cellCenter Q) r)
  have ha : Measurable a := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro r
    exact (measurable_const.mul (measurable_pi_apply r |>.comp measurable_snd)).add
      ((measurable_pi_apply r).comp ((continuous_exactLabel n).measurable.comp
        (measurable_fst.prodMk measurable_const)))
  let g := fun q w => rule.prob (a q) w
  have h := normalized_block_information (n := n) (k := n/16) (m := n/8)
    (by omega) (by omega) (by omega) (by omega) (by omega) Q μ hsupport hB hspread
    g (fun w => (rule.measurable_prob w).comp ha) (fun q w => rule.nonneg (a q) w)
    (fun q => rule.sum_one (a q))
  have heg (w : Fin N) (z : Coordinate n) (X : GaussianBlock n) :
      g (X,projectVector X (normalizedChart Q z)) w = rule.prob (X,exactLabel X z) w := by
    dsimp [g,a]
    rw [exactLabel_normalization]
  simp_rw [heg] at h
  simpa only [gaussianRows,gaussianBlockLaw,blockProbability,Fintype.card_fin] using h

end RepeatedLocalization

end OAI
