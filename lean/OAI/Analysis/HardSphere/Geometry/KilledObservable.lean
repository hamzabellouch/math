import Mathlib
import OAI.Analysis.HardSphere.Operators.FreeTransition
import OAI.Analysis.HardSphere.Bridges.NormalizedPrefix

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener
open scoped ComplexConjugate

def killedObservable (N : ℕ) (L : Length) (a : ℝ)
    (g : Configuration N L → ℂ) (ω : ConfigurationPath N L) : ℂ :=
  (staysAllowed N L a).indicator (fun ω ↦ g (ω 1)) ω

lemma killedObservable_measurable (N : ℕ) (L : Length) (a : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g) :
    Measurable (killedObservable N L a g) :=
  (hg.comp (continuous_eval_const (1:Time)).measurable).indicator
    (staysAllowed_open N L a).measurableSet

lemma killedObservable_bound (N : ℕ) (L : Length) (a : ℝ)
    {g : Configuration N L → ℂ} {C : ℝ} (hC : 0≤C) (hg : ∀ X, ‖g X‖≤C)
    (ω : ConfigurationPath N L) : ‖killedObservable N L a g ω‖≤C := by
  by_cases ha : ω∈staysAllowed N L a
  · simpa only [killedObservable,Set.indicator_of_mem ha] using hg (ω 1)
  · simpa only [killedObservable,Set.indicator_of_notMem ha,norm_zero] using hC

def killedAverage (N : ℕ) (L : Length) (a t : ℝ)
    (g : Configuration N L → ℂ) (X : Configuration N L) : ℂ :=
  ∫ w, killedObservable N L a g (freeTrajectory N L t w X) ∂coordinateWiener N

lemma killedAverage_measurable (N : ℕ) (L : Length) (a t : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g) :
    Measurable (killedAverage N L a t g) := by
  exact (((killedObservable_measurable N L a hg).comp
    (freeTrajectory_continuous N L t).measurable).stronglyMeasurable.integral_prod_left').measurable

lemma killedAverage_bound (N : ℕ) (L : Length) (a t : ℝ)
    {g : Configuration N L → ℂ} {C : ℝ} (hC : 0≤C) (hg : ∀ X, ‖g X‖≤C)
    (X : Configuration N L) : ‖killedAverage N L a t g X‖≤C := by
  simpa only [killedAverage,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const (μ := coordinateWiener N)
      (Filter.Eventually.of_forall fun w ↦ killedObservable_bound N L a hC hg
        (freeTrajectory N L t w X))

lemma killedAverage_memLp (N : ℕ) (L : Length) (a t : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    MemLp (killedAverage N L a t g) 2 (volume : Measure (Configuration N L)) :=
  MemLp.of_bound (killedAverage_measurable N L a t hg).aestronglyMeasurable C
    (Filter.Eventually.of_forall (killedAverage_bound N L a t hC hgC))

lemma integrable_killedAverage_pairing (N : ℕ) (L : Length) (a t : ℝ)
    (f : C(Configuration N L,ℂ)) {g : Configuration N L → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    Integrable (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f p.2) * killedObservable N L a g (freeTrajectory N L t p.1 p.2))
      ((coordinateWiener N).prod volume) := by
  refine (integrable_const (‖f‖*C)).mono' ?_ ?_
  · exact (((f.continuous.comp continuous_snd).star.measurable).mul
      ((killedObservable_measurable N L a hg).comp
        (freeTrajectory_continuous N L t).measurable)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p ↦ by
      rw [norm_mul,RCLike.norm_conj]
      exact mul_le_mul (f.norm_coe_le_norm p.2)
        (killedObservable_bound N L a hC hgC _) (norm_nonneg _) (norm_nonneg _)

lemma killedTransition_bounded_pairing (N : ℕ) (L : Length) (a t : ℝ)
    (f : C(Configuration N L,ℂ)) {g : Configuration N L → ℂ} (hg : Measurable g)
    (hgLp : MemLp g 2 (volume : Measure (Configuration N L)))
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (killedTransition N L a t (hgLp.toLp g)) =
      ∫ X, conj (f X) * killedAverage N L a t g X := by
  rw [killedTransition_pairing,killedPathLaw,← integral_indicator (staysAllowed_open N L a).measurableSet]
  have he : (staysAllowed N L a).indicator (fun ω : ConfigurationPath N L ↦
      conj (ContinuousMap.toLp 2 volume ℂ f (ω 0)) * hgLp.toLp g (ω 1)) =ᵐ[freePathLaw N L t]
      (fun ω ↦ conj (f (ω 0)) * killedObservable N L a g ω) := by
    filter_upwards [(freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae
        (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f),
      (freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae hgLp.coeFn_toLp] with ω hf hg'
    by_cases ha : ω∈staysAllowed N L a
    · simp only [Set.indicator_of_mem ha,killedObservable,hf,hg']
    · simp only [Set.indicator_of_notMem ha,killedObservable,mul_zero]
  rw [integral_congr_ae he,freePathLaw]
  have hm : Measurable (fun ω : ConfigurationPath N L ↦
      conj (f (ω 0)) * killedObservable N L a g ω) := by
    exact (f.continuous.comp (continuous_eval_const (0:Time))).star.measurable.mul
      (killedObservable_measurable N L a hg)
  rw [integral_map (freeTrajectory_continuous N L t).measurable.aemeasurable hm.aestronglyMeasurable]
  have hzero : (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f (freeTrajectory N L t p.1 p.2 0)) * killedObservable N L a g (freeTrajectory N L t p.1 p.2)) =ᵐ[
        (coordinateWiener N).prod volume]
      (fun p ↦ conj (f p.2) * killedObservable N L a g (freeTrajectory N L t p.1 p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (freeTrajectory_initial_ae N L t)] with p hp
    rw [hp]
  rw [integral_congr_ae hzero,integral_prod_symm _ (integrable_killedAverage_pairing N L a t f hg hC hgC)]
  simp_rw [integral_const_mul]
  rfl

lemma killedTransition_bounded (N : ℕ) (L : Length) (a t : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g)
    (hgLp : MemLp g 2 (volume : Measure (Configuration N L)))
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    killedTransition N L a t (hgLp.toLp g) =
      (killedAverage_memLp N L a t hg hC hgC).toLp (killedAverage N L a t g) := by
  apply ext_inner_left ℂ
  intro f
  have hd := ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)
  have hc : IsClosed {f : ScalarL2 N L |
      inner ℂ f (killedTransition N L a t (hgLp.toLp g)) =
        inner ℂ f ((killedAverage_memLp N L a t hg hC hgC).toLp (killedAverage N L a t g))} :=
    isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  apply hc.closure_subset_iff.mpr ?_ (hd f)
  rintro _ ⟨f,rfl⟩
  change inner ℂ _ _ = inner ℂ _ _
  rw [killedTransition_bounded_pairing N L a t f hg hgLp hC hgC,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f,
    (killedAverage_memLp N L a t hg hC hgC).coeFn_toLp] with X hf hX
  rw [RCLike.inner_apply,hf,hX,mul_comm]

def splitObservable (N : ℕ) (L : Length) (a : ℝ) (g : Configuration N L → ℂ)
    (p : ConfigurationPath N L × ConfigurationPath N L) : ℂ := by
  classical
  exact if p.1∈staysAllowed N L a then killedObservable N L a g p.2 else 0

lemma splitObservable_measurable (N : ℕ) (L : Length) (a : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g) :
    Measurable (splitObservable N L a g) := by
  exact Measurable.ite ((staysAllowed_open N L a).measurableSet.preimage measurable_fst)
    ((killedObservable_measurable N L a hg).comp measurable_snd) measurable_const

lemma splitObservable_bound (N : ℕ) (L : Length) (a : ℝ)
    {g : Configuration N L → ℂ} {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C)
    (p : ConfigurationPath N L × ConfigurationPath N L) :
    ‖splitObservable N L a g p‖≤C := by
  by_cases h : p.1∈staysAllowed N L a
  · simpa only [splitObservable,ite_eq_left h] using killedObservable_bound N L a hC hgC p.2
  · simpa only [splitObservable,ite_eq_right h,norm_zero] using hC

lemma killedObservable_split (N : ℕ) (L : Length) (a : ℝ)
    (g : Configuration N L → ℂ) (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1)
    (ω : ConfigurationPath N L) :
    killedObservable N L a g ω = splitObservable N L a g
      (configurationPrefix N L u ω,configurationSuffix N L u ω) := by
  have he := staysAllowed_split N L a u hu hu' ω
  have hend : configurationSuffix N L u ω 1=ω 1 := by
    simp only [configurationSuffix,ContinuousMap.comp_apply,suffixTime_one]
  by_cases hp : configurationPrefix N L u ω∈staysAllowed N L a
  · by_cases hq : configurationSuffix N L u ω∈staysAllowed N L a
    · simp [killedObservable,splitObservable,hp,hq,he.mpr ⟨hp,hq⟩,hend]
    · have h : ω∉staysAllowed N L a := fun h ↦ hq (he.mp h).2
      simp [killedObservable,splitObservable,h,hp,hq]
  · have h : ω∉staysAllowed N L a := fun h ↦ hp (he.mp h).1
    simp [killedObservable,splitObservable,h,hp]

lemma split_fixedTrajectory_measurable (N : ℕ) (L : Length) (s t : ℝ)
    (X : Configuration N L) :
    Measurable (fun p : CoordinatePaths N × CoordinatePaths N ↦
      (freeTrajectory N L s p.1 X,
        freeTrajectory N L t p.2 (freeTrajectory N L s p.1 X 1))) := by
  exact ((freeTrajectory_continuous N L s |>.comp (continuous_fst.prodMk continuous_const)).prodMk
    (freeTrajectory_continuous N L t |>.comp (continuous_snd.prodMk
      ((freeTrajectory_continuous N L s |>.comp (continuous_fst.prodMk continuous_const)).eval continuous_const)))).measurable

lemma split_fixedTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0<s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    (configurationPrefix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X),
      configurationSuffix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X)) =
      (freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X,
        freeTrajectory N L t (fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p))
          (freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X 1)) := by
  apply Prod.ext
  · exact prefix_freeTrajectory N L s t hs ht w X
  · dsimp only [Prod.snd]
    rw [suffix_freeTrajectory N L s t hs ht]
    congr 1
    have heq := congrArg (fun ω : ConfigurationPath N L ↦ ω 1)
      (prefix_freeTrajectory N L s t hs ht w X)
    simpa only [configurationPrefix,ContinuousMap.comp_apply,prefixTime_one] using heq

lemma killedAverage_add (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0<s) (ht : 0<t)
    {g : Configuration N L → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) (X : Configuration N L) :
    killedAverage N L a (s+t) g X =
      killedAverage N L a s (killedAverage N L a t g) X := by
  let F : CoordinatePaths N × CoordinatePaths N → ℂ := fun p ↦
    splitObservable N L a g (freeTrajectory N L s p.1 X,
      freeTrajectory N L t p.2 (freeTrajectory N L s p.1 X 1))
  have hm : Measurable F := (splitObservable_measurable N L a hg).comp
    (split_fixedTrajectory_measurable N L s t X)
  have hb : ∀ p, ‖F p‖≤C := fun p ↦ splitObservable_bound N L a hC hgC _
  have hi : Integrable F ((coordinateWiener N).prod (coordinateWiener N)) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hsplit := coordinateSplit_preserving N (splitTime s t hs ht)
    (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)
  calc
    _ = ∫ w, F (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p),
          fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) ∂coordinateWiener N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        dsimp only []
        rw [killedObservable_split N L a g (splitTime s t hs ht)
          (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht),split_fixedTrajectory]
    _ = ∫ p, F p ∂(coordinateWiener N).prod (coordinateWiener N) := by
      rw [← hsplit.map_eq,integral_map hsplit.measurable.aemeasurable hm.aestronglyMeasurable]
    _ = ∫ w, ∫ w', F (w,w') ∂coordinateWiener N ∂coordinateWiener N := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        change (∫ w', splitObservable N L a g
          (freeTrajectory N L s w X,freeTrajectory N L t w' (freeTrajectory N L s w X 1))
            ∂coordinateWiener N) =
          killedObservable N L a (killedAverage N L a t g) (freeTrajectory N L s w X)
        by_cases h : freeTrajectory N L s w X∈staysAllowed N L a
        · simp only [splitObservable,ite_eq_left h,killedObservable,Set.indicator_of_mem h]
          rfl
        · simp only [splitObservable,ite_eq_right h,killedObservable,Set.indicator_of_notMem h,integral_zero]

end HardSphere

end

end OAI
