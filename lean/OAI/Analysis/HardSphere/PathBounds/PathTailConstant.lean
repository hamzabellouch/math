import Mathlib
import OAI.Analysis.HardSphere.Fourier.CharacterDerivativeFactor
import OAI.Analysis.HardSphere.Geometry.KilledObservable
import OAI.Analysis.HardSphere.Bridges.Moment8

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open Wiener

lemma staysAllowed_of_neg (N : ℕ) (L : Length) {a : ℝ} (ha : a<0) :
    staysAllowed N L a=Set.univ := by
  ext ω
  simp only [staysAllowed,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  rw [allowed_of_neg N L ha]
  exact Set.subset_univ _

lemma killedObservable_of_neg (N : ℕ) (L : Length) {a : ℝ} (ha : a<0)
    (g : Configuration N L → ℂ) (ω : ConfigurationPath N L) :
    killedObservable N L a g ω=g (ω 1) := by
  simp only [killedObservable,staysAllowed_of_neg N L ha,Set.indicator_univ]

lemma killedTransition_of_neg (N : ℕ) (L : Length) {a : ℝ} (ha : a<0) (t : ℝ) :
    killedTransition N L a t=freeTransition N L t := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [killedTransition_pairing,freeTransition_pairing]
  simp only [killedPathLaw,staysAllowed_of_neg N L ha,Measure.restrict_univ]

lemma freeTrajectory_dist_le (N : ℕ) (L : Length) (t : ℝ)
    {w : CoordinatePaths N} {B : ℝ} (hB : 0≤B)
    (hw : ∀ p, ‖w p‖≤B) (X : Configuration N L) (s u : Time) :
    dist (freeTrajectory N L t w X s) (freeTrajectory N L t w X u) ≤
      2*Real.sqrt (2*t)*B := by
  have hC : 0≤2*Real.sqrt (2*t)*B := by positivity
  apply (dist_pi_le_iff hC).mpr
  intro i
  apply (dist_pi_le_iff hC).mpr
  intro j
  change dist (X i j+((Real.sqrt (2*t)*w (i,j) s : ℝ):AddCircle L.val))
    (X i j+((Real.sqrt (2*t)*w (i,j) u : ℝ):AddCircle L.val))≤_
  rw [dist_add_left,dist_eq_norm,← QuotientAddGroup.mk_sub]
  calc
    _ ≤ ‖Real.sqrt (2*t)*w (i,j) s-Real.sqrt (2*t)*w (i,j) u‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ = Real.sqrt (2*t)*‖w (i,j) s-w (i,j) u‖ := by
      rw [← mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt (2*t)*(B+B) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact (norm_sub_le _ _).trans (add_le_add
        ((w (i,j)).norm_coe_le_norm s |>.trans (hw (i,j)))
        ((w (i,j)).norm_coe_le_norm u |>.trans (hw (i,j))))
    _ = _ := by ring

lemma killedObservable_eq_of_small_path (N : ℕ) (L : Length) (a t : ℝ)
    (g : Configuration N L → ℂ) {δ B : ℝ} (hB : 0≤B)
    (hδ : Metric.cthickening δ (tsupport g) ⊆ allowed N L a)
    (ht : 2*Real.sqrt (2*t)*B≤δ)
    {w : CoordinatePaths N} (hw : ∀ p, ‖w p‖≤B) (X : Configuration N L) :
    killedObservable N L a g (freeTrajectory N L t w X)=g (freeTrajectory N L t w X 1) := by
  by_cases hg : g (freeTrajectory N L t w X 1)=0
  · simp only [killedObservable]
    by_cases he : freeTrajectory N L t w X∈staysAllowed N L a
    · simp only [Set.indicator_of_mem he]
    · simp only [Set.indicator_of_notMem he,hg]
  · have hs : freeTrajectory N L t w X 1∈tsupport g := subset_closure hg
    have he : freeTrajectory N L t w X∈staysAllowed N L a := by
      rintro _ ⟨s,rfl⟩
      apply hδ
      exact Metric.mem_cthickening_of_dist_le _ _ _ _ hs
        ((freeTrajectory_dist_le N L t hB hw X s 1).trans ht)
    simp only [killedObservable,Set.indicator_of_mem he]

lemma coordinateWiener_tail8 (N : ℕ) {B : ℝ} (hB : 0<B) :
    coordinateWiener N {w | ∃ p, B*normMultiplier<‖w p‖} ≤
      (Fintype.card (Direction N):ℝ≥0∞)*(ENNReal.ofReal B)⁻¹^8 *
        ((1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8) := by
  have he : {w : CoordinatePaths N | ∃ p, B*normMultiplier<‖w p‖} =
      ⋃ p : Direction N, {w | B*normMultiplier<‖w p‖} := by ext w; simp
  rw [he]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc
    _ = ∑ _p : Direction N, wiener {w | B*normMultiplier<‖w‖} := by
      apply Finset.sum_congr rfl
      intro p _
      exact (measurePreserving_eval (fun _ : Direction N ↦ wiener) p).measure_preimage
        (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet
    _ ≤ ∑ _p : Direction N, (ENNReal.ofReal B)⁻¹^8 *
        ((1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8) :=
      Finset.sum_le_sum fun _ _ ↦ norm_wiener_tail8 hB
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]

lemma killedAverage_free_bound (N : ℕ) (L : Length) (a t : ℝ)
    (g : C(Configuration N L,ℂ)) {δ B : ℝ} (hB : 0<B)
    (hδ : Metric.cthickening δ (tsupport g) ⊆ allowed N L a)
    (ht : 2*Real.sqrt (2*t)*(B*normMultiplier)≤δ) (X : Configuration N L) :
    ‖killedAverage N L a t g X-killedAverage N L (-1) t g X‖ ≤
      ‖g‖*(coordinateWiener N).real {w | ∃ p, B*normMultiplier<‖w p‖} := by
  let E : Set (CoordinatePaths N) := {w | ∃ p, B*normMultiplier<‖w p‖}
  have hE : MeasurableSet E := by
    have he : E = ⋃ p : Direction N, {w : CoordinatePaths N | B*normMultiplier<‖w p‖} := by ext w; simp [E]
    rw [he]
    apply MeasurableSet.iUnion
    intro p
    exact measurableSet_lt measurable_const (measurable_pi_apply p |>.norm)
  have hi (b : ℝ) : Integrable (fun w : CoordinatePaths N ↦
      killedObservable N L b g (freeTrajectory N L t w X)) (coordinateWiener N) := by
    apply (integrable_const ‖g‖).mono'
    · exact ((killedObservable_measurable N L b g.continuous.measurable).comp
        ((freeTrajectory_continuous N L t).comp (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable
    · exact Eventually.of_forall fun _ ↦ killedObservable_bound N L b (norm_nonneg g) g.norm_coe_le_norm _
  rw [killedAverage,killedAverage,← integral_sub (hi a) (hi (-1))]
  calc
    _ ≤ ∫ w, E.indicator (fun _ ↦ ‖g‖) w ∂coordinateWiener N := by
      apply norm_integral_le_of_norm_le
      · exact (integrable_const ‖g‖).indicator hE
      · filter_upwards [] with w
        rw [killedObservable_of_neg N L (by norm_num : (-1:ℝ)<0)]
        by_cases he : w∈E
        · rw [Set.indicator_of_mem he]
          by_cases ha : freeTrajectory N L t w X∈staysAllowed N L a
          · simp only [killedObservable,Set.indicator_of_mem ha,sub_self,norm_zero]
            exact norm_nonneg g
          · simp only [killedObservable,Set.indicator_of_notMem ha,zero_sub,norm_neg]
            exact g.norm_coe_le_norm _
        · rw [Set.indicator_of_notMem he]
          have hw : ∀ p, ‖w p‖≤B*normMultiplier := by
            intro p
            exact le_of_not_gt fun h ↦ he ⟨p,h⟩
          rw [killedObservable_eq_of_small_path N L a t g
            (mul_nonneg hB.le normMultiplier_pos.le) hδ ht hw X,sub_self,norm_zero]
    _ = _ := by rw [integral_indicator_const _ hE]; simp only [smul_eq_mul,mul_comm]; rfl

def pathTailConstant (N : ℕ) : ℝ :=
  ((Fintype.card (Direction N) : ℝ≥0∞) *
    ((1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8)).toReal

lemma pathTailConstant_nonneg (N : ℕ) : 0 ≤ pathTailConstant N := ENNReal.toReal_nonneg

lemma coordinateWiener_tail8_real (N : ℕ) {B : ℝ} (hB : 0<B) :
    (coordinateWiener N).real {w | ∃ p, B*normMultiplier<‖w p‖} ≤
      pathTailConstant N * B⁻¹^8 := by
  have hfin : (Fintype.card (Direction N) : ℝ≥0∞) * (ENNReal.ofReal B)⁻¹^8 *
      ((1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8) ≠ ∞ := by
    apply ENNReal.mul_ne_top _ norm_wiener_tail_constant_finite
    apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    apply ENNReal.pow_ne_top
    rw [ENNReal.inv_ne_top]
    simpa using hB
  have h := ENNReal.toReal_mono hfin (coordinateWiener_tail8 N hB)
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hB.le, pathTailConstant,mul_assoc,mul_left_comm,mul_comm] using h

lemma killedAverage_free_order4 (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) {δ : ℝ} (hδpos : 0<δ)
    (hδ : Metric.cthickening δ (tsupport g) ⊆ allowed N L a)
    {t : ℝ} (ht : 0<t) (X : Configuration N L) :
    ‖killedAverage N L a t g X-killedAverage N L (-1) t g X‖ ≤
      (‖g‖*pathTailConstant N*(2*normMultiplier/δ)^8*16)*t^4 := by
  let B : ℝ := δ/(2*Real.sqrt (2*t)*normMultiplier)
  have hs : 0<Real.sqrt (2*t) := Real.sqrt_pos.2 (by positivity)
  have hB : 0<B := div_pos hδpos (mul_pos (mul_pos (by norm_num) hs) normMultiplier_pos)
  have hBt : 2*Real.sqrt (2*t)*(B*normMultiplier)≤δ := by
    dsimp [B]
    have hn := normMultiplier_pos.ne'
    field_simp
    exact le_rfl
  calc
    _ ≤ ‖g‖*(coordinateWiener N).real {w | ∃ p, B*normMultiplier<‖w p‖} :=
      killedAverage_free_bound N L a t g hB hδ hBt X
    _ ≤ ‖g‖*(pathTailConstant N*B⁻¹^8) :=
      mul_le_mul_of_nonneg_left (coordinateWiener_tail8_real N hB) (norm_nonneg g)
    _ = _ := by
      have hsq := Real.sq_sqrt (by positivity : 0≤2*t)
      dsimp [B]
      rw [inv_div]
      calc
        _ = ‖g‖ * pathTailConstant N * (2 * normMultiplier / δ)^8 *
            (Real.sqrt (2*t)^2)^4 := by ring
        _ = _ := by rw [hsq]; ring

lemma killedTransition_continuous_ae_core (N : ℕ) (L : Length) (a t : ℝ)
    (g : C(Configuration N L,ℂ)) :
    killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g) =ᵐ[volume]
      killedAverage N L a t g := by
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  rw [hge,killedTransition_bounded N L a t g.continuous.measurable
    hgLp (norm_nonneg g) g.norm_coe_le_norm]
  exact MemLp.coeFn_toLp _

lemma killedTransition_free_order4 (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) (hg : tsupport g⊆allowed N L a) :
    ∃ C : ℝ, 0≤C ∧ ∀ t : ℝ, 0<t →
      ‖killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g)-
        freeTransition N L t (ContinuousMap.toLp 2 volume ℂ g)‖ ≤ C*t^4 := by
  obtain ⟨δ,hδpos,hδ⟩ := (isClosed_tsupport g).isCompact.exists_cthickening_subset_open
    (isOpen_allowed N L a) hg
  let C0 : ℝ := ‖g‖*pathTailConstant N*(2*normMultiplier/δ)^8*16
  have hC0 : 0≤C0 := by
    have hp := pathTailConstant_nonneg N
    dsimp [C0]
    positivity
  let M : ℝ := (measureUnivNNReal (volume : Measure (Configuration N L)) : ℝ) ^ (2:ℝ≥0∞).toReal⁻¹
  have hM : 0≤M := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  refine ⟨M*C0,mul_nonneg hM hC0,?_⟩
  intro t ht
  rw [← killedTransition_of_neg N L (by norm_num : (-1:ℝ)<0)]
  have hb : ∀ᵐ X ∂(volume : Measure (Configuration N L)),
      ‖(killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g)-
        killedTransition N L (-1) t (ContinuousMap.toLp 2 volume ℂ g)) X‖≤C0*t^4 := by
    filter_upwards [Lp.coeFn_sub (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))
      (killedTransition N L (-1) t (ContinuousMap.toLp 2 volume ℂ g)),
      killedTransition_continuous_ae_core N L a t g,killedTransition_continuous_ae_core N L (-1) t g] with X hsub ha hb
    rw [hsub,Pi.sub_apply,ha,hb]
    exact killedAverage_free_order4 N L a g hδpos hδ ht X
  exact (Lp.norm_le_of_ae_bound (mul_nonneg hC0 (by positivity)) hb).trans_eq (by dsimp [M]; ring)

lemma killedTransition_free_firstOrder (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) (hg : tsupport g⊆allowed N L a) :
    Tendsto (fun t : ℝ ↦ (t⁻¹:ℝ) •
      (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g)-
        freeTransition N L t (ContinuousMap.toLp 2 volume ℂ g)))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := killedTransition_free_order4 N L a g hg
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun t : ℝ ↦ C*t^3) (Eventually.of_forall fun t ↦ norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0<t := ht
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht')]
    calc
      _ ≤ t⁻¹*(C*t^4) := mul_le_mul_of_nonneg_left (hb t ht') (by positivity)
      _ = C*t^3 := by field_simp
  · have h := (tendsto_const_nhds (x := C)).mul
      ((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)).pow 3)
    simpa using h.mono_left nhdsWithin_le_nhds

end HardSphere

end

end OAI
