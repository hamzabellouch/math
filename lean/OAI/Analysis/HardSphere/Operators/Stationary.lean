import Mathlib
import OAI.Analysis.HardSphere.Comparison.DensityForcesTwoParticles
import OAI.Analysis.HardSphere.Geometry.GroundPathWeight

namespace OAI

namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate ENNReal Topology BigOperators
noncomputable section
variable {N : ℕ} {L : Length}

def weightedKilledTransition (N : ℕ) (L : Length) (a t : ℝ)
    (h : ConfigurationPath N L → ℂ) (hh : MemLp h ∞ (freePathLaw N L t)) :
    ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  (endpointPull N L t 0).toContinuousLinearMap.adjoint ∘L
    (L2Multiplier.clm h hh ∘L (avoidanceMultiplier N L a t ∘L
      (endpointPull N L t 1).toContinuousLinearMap))

lemma weightedKilledTransition_pairing (N : ℕ) (L : Length) (a t : ℝ)
    (h : ConfigurationPath N L → ℂ) (hh : MemLp h ∞ (freePathLaw N L t))
    (f g : ScalarL2 N L) :
    inner ℂ f (weightedKilledTransition N L a t h hh g) =
      ∫ ω, conj (f (ω 0)) * (h ω*g (ω 1)) ∂killedPathLaw N L a t := by
  rw [weightedKilledTransition,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,L2.inner_def]
  change (∫ ω, inner ℂ (endpointPull N L t 0 f ω)
    (L2Multiplier.clm h hh (avoidanceMultiplier N L a t (endpointPull N L t 1 g)) ω)
      ∂freePathLaw N L t)=_
  rw [killedPathLaw,← integral_indicator (staysAllowed_open N L a).measurableSet]
  apply integral_congr_ae
  filter_upwards [endpointPull_ae N L t 0 f,endpointPull_ae N L t 1 g,
    L2Multiplier.coe_clm h hh (avoidanceMultiplier N L a t (endpointPull N L t 1 g)),
    avoidanceMultiplier_ae N L a t (endpointPull N L t 1 g)] with ω hf hg hh' ha
  rw [hh',ha,hf]
  by_cases hω : ω∈staysAllowed N L a
  · simp only [Set.indicator_of_mem hω,hg,RCLike.inner_apply,mul_comm]
  · simp only [Set.indicator_of_notMem hω,mul_zero,inner_zero_right]

def weightedKilledAverage (N : ℕ) (L : Length) (a t : ℝ)
    (h : ConfigurationPath N L → ℂ) (g : Configuration N L → ℂ)
    (X : Configuration N L) : ℂ :=
  ∫ w, h (freeTrajectory N L t w X)*
    killedObservable N L a g (freeTrajectory N L t w X) ∂coordinateWiener N

lemma weightedKilledAverage_measurable (N : ℕ) (L : Length) (a t : ℝ)
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    {g : Configuration N L → ℂ} (hg : Measurable g) :
    Measurable (weightedKilledAverage N L a t h g) := by
  exact (((hh.mul (killedObservable_measurable N L a hg)).comp
    (freeTrajectory_continuous N L t).measurable).stronglyMeasurable.integral_prod_left').measurable

lemma weightedKilledAverage_bound (N : ℕ) (L : Length) (a t : ℝ)
    {h : ConfigurationPath N L → ℂ} {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B)
    {g : Configuration N L → ℂ} {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C)
    (X : Configuration N L) : ‖weightedKilledAverage N L a t h g X‖≤B*C := by
  have hb (w : CoordinatePaths N) : ‖h (freeTrajectory N L t w X)*
      killedObservable N L a g (freeTrajectory N L t w X)‖≤B*C := by
    rw [norm_mul]
    exact mul_le_mul (hhB _) (killedObservable_bound N L a hC hgC _) (norm_nonneg _) hB
  simpa only [weightedKilledAverage,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const (μ := coordinateWiener N) (Eventually.of_forall hb)

lemma weightedKilledAverage_memLp (N : ℕ) (L : Length) (a t : ℝ)
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B)
    {g : Configuration N L → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    MemLp (weightedKilledAverage N L a t h g) 2 (volume : Measure (Configuration N L)) :=
  MemLp.of_bound (weightedKilledAverage_measurable N L a t hh hg).aestronglyMeasurable (B*C)
    (Eventually.of_forall (weightedKilledAverage_bound N L a t hB hhB hC hgC))

lemma integrable_weightedAverage_pairing (N : ℕ) (L : Length) (a t : ℝ)
    (f : C(Configuration N L,ℂ))
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B)
    {g : Configuration N L → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    Integrable (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f p.2) * (h (freeTrajectory N L t p.1 p.2)*
        killedObservable N L a g (freeTrajectory N L t p.1 p.2)))
      ((coordinateWiener N).prod volume) := by
  refine (integrable_const (‖f‖*(B*C))).mono' ?_ ?_
  · exact (((f.continuous.comp continuous_snd).star.measurable).mul
      ((hh.mul (killedObservable_measurable N L a hg)).comp
        (freeTrajectory_continuous N L t).measurable)).aestronglyMeasurable
  · exact Eventually.of_forall fun p ↦ by
      simp only [norm_mul,RCLike.norm_conj]
      exact mul_le_mul (f.norm_coe_le_norm p.2)
        (mul_le_mul (hhB _) (killedObservable_bound N L a hC hgC _) (norm_nonneg _) hB)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

lemma weightedKilledTransition_bounded_pairing (N : ℕ) (L : Length) (a t : ℝ)
    (f : C(Configuration N L,ℂ))
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    (hhLp : MemLp h ∞ (freePathLaw N L t))
    {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B)
    {g : Configuration N L → ℂ} (hg : Measurable g)
    (hgLp : MemLp g 2 (volume : Measure (Configuration N L)))
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f)
      (weightedKilledTransition N L a t h hhLp (hgLp.toLp g)) =
      ∫ X, conj (f X) * weightedKilledAverage N L a t h g X := by
  rw [weightedKilledTransition_pairing,killedPathLaw,
    ← integral_indicator (staysAllowed_open N L a).measurableSet]
  have he : (staysAllowed N L a).indicator (fun ω : ConfigurationPath N L ↦
      conj (ContinuousMap.toLp 2 volume ℂ f (ω 0)) * (h ω*hgLp.toLp g (ω 1))) =ᵐ[freePathLaw N L t]
      (fun ω ↦ conj (f (ω 0)) * (h ω*killedObservable N L a g ω)) := by
    filter_upwards [(freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae
        (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f),
      (freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae hgLp.coeFn_toLp] with ω hf hg'
    by_cases ha : ω∈staysAllowed N L a
    · simp only [Set.indicator_of_mem ha,killedObservable,hf,hg']
    · simp only [Set.indicator_of_notMem ha,killedObservable,mul_zero]
  rw [integral_congr_ae he,freePathLaw]
  have hm : Measurable (fun ω : ConfigurationPath N L ↦
      conj (f (ω 0)) * (h ω*killedObservable N L a g ω)) := by
    exact (f.continuous.comp (continuous_eval_const (0:Time))).star.measurable.mul
      (hh.mul (killedObservable_measurable N L a hg))
  rw [integral_map (freeTrajectory_continuous N L t).measurable.aemeasurable hm.aestronglyMeasurable]
  have hzero : (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f (freeTrajectory N L t p.1 p.2 0)) *
        (h (freeTrajectory N L t p.1 p.2)*killedObservable N L a g (freeTrajectory N L t p.1 p.2))) =ᵐ[
        (coordinateWiener N).prod volume]
      (fun p ↦ conj (f p.2) * (h (freeTrajectory N L t p.1 p.2)*
        killedObservable N L a g (freeTrajectory N L t p.1 p.2))) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (freeTrajectory_initial_ae N L t)] with p hp
    rw [hp]
  rw [integral_congr_ae hzero,
    integral_prod_symm _ (integrable_weightedAverage_pairing N L a t f hh hB hhB hg hC hgC)]
  simp_rw [integral_const_mul]
  rfl

lemma weightedKilledTransition_bounded (N : ℕ) (L : Length) (a t : ℝ)
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    (hhLp : MemLp h ∞ (freePathLaw N L t))
    {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B)
    {g : Configuration N L → ℂ} (hg : Measurable g)
    (hgLp : MemLp g 2 (volume : Measure (Configuration N L)))
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    weightedKilledTransition N L a t h hhLp (hgLp.toLp g) =
      (weightedKilledAverage_memLp N L a t hh hB hhB hg hC hgC).toLp
        (weightedKilledAverage N L a t h g) := by
  apply ext_inner_left ℂ
  intro f
  have hd := ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)
  have hc : IsClosed {f : ScalarL2 N L |
      inner ℂ f (weightedKilledTransition N L a t h hhLp (hgLp.toLp g)) =
        inner ℂ f ((weightedKilledAverage_memLp N L a t hh hB hhB hg hC hgC).toLp
          (weightedKilledAverage N L a t h g))} :=
    isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  apply hc.closure_subset_iff.mpr ?_ (hd f)
  rintro _ ⟨f,rfl⟩
  change inner ℂ _ _ = inner ℂ _ _
  rw [weightedKilledTransition_bounded_pairing N L a t f hh hhLp hB hhB hg hgLp hC hgC,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f,
    (weightedKilledAverage_memLp N L a t hh hB hhB hg hC hgC).coeFn_toLp] with X hf hX
  rw [RCLike.inner_apply,hf,hX,mul_comm]

end

noncomputable section

lemma weightedKilledAverage_prefix (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0<s) (ht : 0<t)
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B)
    {g : Configuration N L → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) (X : Configuration N L) :
    weightedKilledAverage N L a (s+t) (h ∘ configurationPrefix N L (splitTime s t hs ht)) g X =
      weightedKilledAverage N L a s h (killedAverage N L a t g) X := by
  let F : CoordinatePaths N × CoordinatePaths N → ℂ := fun p ↦
    h (freeTrajectory N L s p.1 X) * splitObservable N L a g
      (freeTrajectory N L s p.1 X,freeTrajectory N L t p.2 (freeTrajectory N L s p.1 X 1))
  have hm : Measurable F :=
    (hh.comp ((freeTrajectory_continuous N L s).comp (continuous_fst.prodMk continuous_const)).measurable).mul
      ((splitObservable_measurable N L a hg).comp (split_fixedTrajectory_measurable N L s t X))
  have hi : Integrable F ((coordinateWiener N).prod (coordinateWiener N)) := by
    refine (integrable_const (B*C)).mono' hm.aestronglyMeasurable ?_
    exact Eventually.of_forall fun p ↦ by
      rw [norm_mul]
      exact mul_le_mul (hhB _) (splitObservable_bound N L a hC hgC _) (norm_nonneg _) hB
  have hsplit := coordinateSplit_preserving N (splitTime s t hs ht)
    (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)
  calc
    _ = ∫ w, F (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p),
          fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) ∂coordinateWiener N := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w ↦ by
        dsimp only [weightedKilledAverage,Function.comp_def,F]
        rw [killedObservable_split N L a g (splitTime s t hs ht)
          (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht),split_fixedTrajectory,
          prefix_freeTrajectory]
    _ = ∫ p, F p ∂(coordinateWiener N).prod (coordinateWiener N) := by
      rw [← hsplit.map_eq,integral_map hsplit.measurable.aemeasurable hm.aestronglyMeasurable]
    _ = ∫ w, ∫ w', F (w,w') ∂coordinateWiener N ∂coordinateWiener N := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w ↦ by
        change (∫ w', h (freeTrajectory N L s w X)*splitObservable N L a g
          (freeTrajectory N L s w X,freeTrajectory N L t w' (freeTrajectory N L s w X 1))
            ∂coordinateWiener N) = h (freeTrajectory N L s w X)*
          killedObservable N L a (killedAverage N L a t g) (freeTrajectory N L s w X)
        rw [integral_const_mul]
        congr 1
        by_cases hω : freeTrajectory N L s w X∈staysAllowed N L a
        · simp only [splitObservable,ite_eq_left hω,killedObservable,Set.indicator_of_mem hω]
          rfl
        · simp only [splitObservable,ite_eq_right hω,killedObservable,Set.indicator_of_notMem hω,integral_zero]

lemma weightedKilledTransition_prefix (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0<s) (ht : 0<t)
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    (hhLp : MemLp h ∞ (freePathLaw N L s))
    (hpLp : MemLp (h ∘ configurationPrefix N L (splitTime s t hs ht)) ∞ (freePathLaw N L (s+t)))
    {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B) :
    weightedKilledTransition N L a (s+t) (h ∘ configurationPrefix N L (splitTime s t hs ht)) hpLp =
      weightedKilledTransition N L a s h hhLp ∘L killedTransition N L a t := by
  have hd := ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)
  apply ContinuousLinearMap.ext
  intro g
  change weightedKilledTransition N L a (s+t) (h ∘ configurationPrefix N L (splitTime s t hs ht)) hpLp g =
    weightedKilledTransition N L a s h hhLp (killedTransition N L a t g)
  have hc : IsClosed {g : ScalarL2 N L |
      weightedKilledTransition N L a (s+t) (h ∘ configurationPrefix N L (splitTime s t hs ht)) hpLp g =
        weightedKilledTransition N L a s h hhLp (killedTransition N L a t g)} :=
    isClosed_eq (ContinuousLinearMap.continuous _) ((ContinuousLinearMap.continuous _).comp
      (ContinuousLinearMap.continuous _))
  apply hc.closure_subset_iff.mpr ?_ (hd g)
  rintro _ ⟨g,rfl⟩
  change weightedKilledTransition N L a (s+t) (h ∘ configurationPrefix N L (splitTime s t hs ht)) hpLp
      (ContinuousMap.toLp 2 volume ℂ g) =
    weightedKilledTransition N L a s h hhLp (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖ (Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  rw [hge,weightedKilledTransition_bounded N L a (s+t)
      (hh.comp (configurationPrefix_continuous N L _).measurable) hpLp hB
      (fun ω ↦ hhB _) g.continuous.measurable hgLp (norm_nonneg _) g.norm_coe_le_norm,
    killedTransition_bounded N L a t g.continuous.measurable hgLp (norm_nonneg _) g.norm_coe_le_norm,
    weightedKilledTransition_bounded N L a s hh hhLp hB hhB
      (killedAverage_measurable N L a t g.continuous.measurable)
      (killedAverage_memLp N L a t g.continuous.measurable (norm_nonneg _) g.norm_coe_le_norm)
      (norm_nonneg g) (killedAverage_bound N L a t (norm_nonneg _) g.norm_coe_le_norm)]
  apply MemLp.toLp_congr
  exact Eventually.of_forall (weightedKilledAverage_prefix N L a s t hs ht hh hB hhB
    g.continuous.measurable (norm_nonneg _) g.norm_coe_le_norm)

variable {N : ℕ} {L : Length} {a : ℝ}

lemma weightedKilledTransition_indicator_pairing (t : ℝ) (f g : ScalarL2 N L)
    {S : Set (ConfigurationPath N L)} (hS : MeasurableSet S) :
    inner ℂ (modulusScalar f) (weightedKilledTransition N L a t (S.indicator (fun _ ↦ (1:ℂ)))
      ((memLp_top_const (1:ℂ)).indicator hS) (modulusScalar g)) =
      ((∫ ω : ConfigurationPath N L in S, ‖f (ω 0)‖*‖g (ω 1)‖ ∂killedPathLaw N L a t):ℝ) := by
  rw [weightedKilledTransition_pairing,← integral_complex_ofReal,← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [((freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae_eq_comp
      (coe_modulusScalar f)).filter_mono (ae_mono Measure.restrict_le_self),
    ((freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae_eq_comp
      (coe_modulusScalar g)).filter_mono (ae_mono Measure.restrict_le_self)] with ω hf hg
  dsimp only [Function.comp_def] at hf hg
  by_cases hω : ω∈S
  · simp only [Set.indicator_of_mem hω,hf,hg,Complex.conj_ofReal,one_mul,Complex.ofReal_mul]
  · simp only [Set.indicator_of_notMem hω,zero_mul,mul_zero]

lemma IsGroundVector.prefix_norm_setIntegral {u : Jet N L} (hu : IsGroundVector N L a u)
    (s t : ℝ) (hs : 0<s) (ht : 0<t)
    {S : Set (ConfigurationPath N L)} (hS : MeasurableSet S) :
    (∫ ω : ConfigurationPath N L in (configurationPrefix N L (splitTime s t hs ht)) ⁻¹' S,
      ‖u.1 (ω 0)‖*‖u.1 (ω 1)‖ ∂killedPathLaw N L a (s+t)) =
      Real.exp (-t*energy u)*(∫ ω : ConfigurationPath N L in S,
        ‖u.1 (ω 0)‖*‖u.1 (ω 1)‖ ∂killedPathLaw N L a s) := by
  let h : ConfigurationPath N L → ℂ := S.indicator (fun _ ↦ 1)
  have hh : Measurable h := measurable_const.indicator hS
  have hhs : MemLp h ∞ (freePathLaw N L s) := (memLp_top_const (1:ℂ)).indicator hS
  have hhp : MemLp (h ∘ configurationPrefix N L (splitTime s t hs ht)) ∞ (freePathLaw N L (s+t)) := by
    exact (memLp_top_const (1:ℂ)).indicator (hS.preimage (configurationPrefix_continuous N L _).measurable)
  have hb (ω : ConfigurationPath N L) : ‖h ω‖≤1 := by
    by_cases hω : ω∈S <;> simp [h,hω]
  have heq : inner ℂ (modulusScalar u.1)
      (weightedKilledTransition N L a (s+t) (h ∘ configurationPrefix N L (splitTime s t hs ht)) hhp
        (modulusScalar u.1)) =
      (Real.exp (-t*energy u):ℂ)*inner ℂ (modulusScalar u.1)
        (weightedKilledTransition N L a s h hhs (modulusScalar u.1)) := by
    rw [weightedKilledTransition_prefix N L a s t hs ht hh hhs hhp zero_le_one hb,
      ContinuousLinearMap.comp_apply]
    have he := hu.modulus.killed_eigenvector ht.le
    change killedTransition N L a t (modulusScalar u.1)=
      (Real.exp (-t*energy (modulusJet u)):ℂ) • modulusScalar u.1 at he
    rw [hu.energy_modulus] at he
    rw [he,map_smul,inner_smul_right]
  have hp : h ∘ configurationPrefix N L (splitTime s t hs ht)=
      ((configurationPrefix N L (splitTime s t hs ht)) ⁻¹' S).indicator (fun _ ↦ (1:ℂ)) := by
    ext ω
    rfl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,← weightedKilledTransition_indicator_pairing (a := a) s u.1 u.1 hS,
    ← weightedKilledTransition_indicator_pairing (a := a) (s+t) u.1 u.1
      (hS.preimage (configurationPrefix_continuous N L _).measurable)]
  simpa only [hp] using heq

lemma IsGroundVector.groundPathLaw_prefix {u : Jet N L} (hu : IsGroundVector N L a u)
    (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    MeasurePreserving (configurationPrefix N L (splitTime s t hs ht))
      (groundPathLaw N L a (s+t) u) (groundPathLaw N L a s u) := by
  refine ⟨(configurationPrefix_continuous N L _).measurable,Measure.ext fun S hS ↦ ?_⟩
  rw [Measure.map_apply (configurationPrefix_continuous N L _).measurable hS,
    groundPathLaw,groundPathLaw,
    withDensity_apply _ (hS.preimage (configurationPrefix_continuous N L _).measurable),
    withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (groundPathWeight_integrable u a (s+t)).integrableOn
      (Eventually.of_forall (groundPathWeight_nonneg u (s+t))),
    ← ofReal_integral_eq_lintegral_ofReal (groundPathWeight_integrable u a s).integrableOn
      (Eventually.of_forall (groundPathWeight_nonneg u s))]
  congr 1
  simp only [groundPathWeight,integral_const_mul]
  rw [hu.prefix_norm_setIntegral s t hs ht hS,← mul_assoc,← Real.exp_add,
    show (s+t)*energy u+ -t*energy u=s*energy u by ring]

end

noncomputable section
variable {N : ℕ} {L : Length} {a : ℝ}

lemma splitTime_reverse (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    splitTime t s ht hs=reverseTime (splitTime s t hs ht) := by
  apply Subtype.ext
  change t/(t+s)=1-s/(s+t)
  rw [add_comm t s]
  field_simp [ne_of_gt (add_pos hs ht)]
  ring

lemma reverse_prefix_reverse (q : Time) (ω : ConfigurationPath N L) :
    reverseConfigurationPath N L (configurationPrefix N L (reverseTime q)
      (reverseConfigurationPath N L ω))=configurationSuffix N L q ω := by
  apply ContinuousMap.ext
  intro v
  change ω (reverseTime (prefixTime (reverseTime q) (reverseTime v)))=ω (suffixTime q v)
  congr 1
  apply Subtype.ext
  change 1-(1-(q:ℝ))*(1-(v:ℝ))=(q:ℝ)+(1-(q:ℝ))*(v:ℝ)
  ring

lemma IsGroundVector.groundPathLaw_suffix {u : Jet N L} (hu : IsGroundVector N L a u)
    (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    MeasurePreserving (configurationSuffix N L (splitTime s t hs ht))
      (groundPathLaw N L a (s+t) u) (groundPathLaw N L a t u) := by
  have hp : MeasurePreserving (configurationPrefix N L (splitTime t s ht hs))
      (groundPathLaw N L a (s+t) u) (groundPathLaw N L a t u) := by
    simpa only [add_comm t s] using hu.groundPathLaw_prefix t s ht hs
  have h := (groundPathLaw_reversal u a t).comp (hp.comp (groundPathLaw_reversal u a (s+t)))
  simpa only [Function.comp_def,splitTime_reverse s t hs ht,reverse_prefix_reverse] using h

lemma groundPathLaw_absolutelyContinuous (N : ℕ) (L : Length) (a t : ℝ) (u : Jet N L) :
    groundPathLaw N L a t u ≪ freePathLaw N L t :=
  (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

lemma freePathLaw_zero_eval (N : ℕ) (L : Length) (q : Time) :
    ∀ᵐ ω ∂freePathLaw N L 0, ω q=ω 0 := by
  rw [freePathLaw]
  apply (ae_map_iff (freeTrajectory_continuous N L 0).measurable.aemeasurable
    (isClosed_eq (continuous_eval_const q) (continuous_eval_const (0:Time))).measurableSet).mpr
  exact Eventually.of_forall fun p ↦ by
    ext i j
    simp only [freeTrajectory,ContinuousMap.coe_mk,mul_zero,Real.sqrt_zero,zero_mul]

lemma IsGroundVector.groundPathLaw_marginal {u : Jet N L} (hu : IsGroundVector N L a u)
    (T : ℝ) (hT : 0≤T) (q : Time) :
    MeasurePreserving (fun ω : ConfigurationPath N L ↦ ω q)
      (groundPathLaw N L a T u) (groundPositionLaw N L u) := by
  by_cases hzero : T=0
  · subst T
    refine ⟨(continuous_eval_const q).measurable,?_⟩
    rw [Measure.map_congr ((groundPathLaw_absolutelyContinuous N L a 0 u).ae_eq
      (freePathLaw_zero_eval N L q))]
    exact (hu.groundPathLaw_initial le_rfl).map_eq
  have hT' : 0<T := lt_of_le_of_ne hT (Ne.symm hzero)
  by_cases hq0 : q=0
  · subst q
    exact hu.groundPathLaw_initial hT
  by_cases hq1 : q=1
  · subst q
    exact hu.groundPathLaw_terminal hT
  have hq : 0<(q:ℝ) := lt_of_le_of_ne q.property.1 (fun h ↦ hq0 (Subtype.ext h.symm))
  have hq' : (q:ℝ)<1 := lt_of_le_of_ne q.property.2 (fun h ↦ hq1 (Subtype.ext h))
  let s := (q:ℝ)*T
  let t := (1-(q:ℝ))*T
  have hs : 0<s := mul_pos hq hT'
  have ht : 0<t := mul_pos (sub_pos.mpr hq') hT'
  have hsum : s+t=T := by dsimp [s,t]; ring
  have hsplit : splitTime s t hs ht=q := by
    apply Subtype.ext
    change s/(s+t)=(q:ℝ)
    rw [hsum]
    exact mul_div_cancel_right₀ _ hzero
  have hp := (hu.groundPathLaw_terminal hs.le).comp (hu.groundPathLaw_prefix s t hs ht)
  simpa only [Function.comp_def,configurationPrefix,ContinuousMap.comp_apply,prefixTime_one,hsplit,hsum] using hp

lemma IsGroundVector.groundPathLaw_middle {u : Jet N L} (hu : IsGroundVector N L a u)
    (r s t : ℝ) (hr : 0<r) (hs : 0<s) (ht : 0<t) :
    MeasurePreserving
      (configurationSuffix N L (splitTime r s hr hs) ∘
        configurationPrefix N L (splitTime (r+s) t (add_pos hr hs) ht))
      (groundPathLaw N L a ((r+s)+t) u) (groundPathLaw N L a s u) :=
  (hu.groundPathLaw_suffix r s hr hs).comp (hu.groundPathLaw_prefix (r+s) t (add_pos hr hs) ht)

end
end HardSphere

namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped Topology
noncomputable section

lemma IsGroundVector.groundPathLaw_close_event {n : ℕ} (L : Length) {r : ℝ}
    {g : Jet n L} (hg : IsGroundVector n L r g) (T : ℝ) (hT : 0≤T) (q : Time)
    {S : Type*} (v : S → Torus L) (A : Finset S) (s h : ℝ) :
    groundPathLaw n L r T g {ω | ∀ a∈A, h≤((pairCloseLabels L s (v a) (ω q)).card:ℝ)} =
      groundPositionLaw n L g {X | ∀ a∈A, h≤((pairCloseLabels L s (v a) X).card:ℝ)} := by
  have hS : MeasurableSet {X : Configuration n L | ∀ a∈A, h≤((pairCloseLabels L s (v a) X).card:ℝ)} := by
    simpa only [Set.ofPred_forall] using Finset.measurableSet_biInter A (fun a _ ↦
      measurableSet_le (show Measurable (fun _ : Configuration n L ↦ h) from measurable_const)
        (pairCloseLabels_measurable L s (v a)))
  exact (hg.groundPathLaw_marginal T hT q).measure_preimage hS.nullMeasurableSet

theorem spatial_stationary_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (T : ℝ), 0≤T → ∀ (q : Time) (A : Finset (CubeCell K)),
      groundPathLaw n L (α/D) T g {ω | ∀ v∈A,
        θ*D≤((pairCloseLabels L (spatialCloseScale D b) (unitCenter L v) (ω q)).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,htail⟩ := spatial_full_and_bath_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,hlim,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hDfin⟩ := hfin αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K L hL D α hL100 hDeq hD hα hαmax g hg T hT q A
  rw [hg.groundPathLaw_close_event L T hT q (unitCenter L) A]
  exact (hDfin n K L hL D α hL100 hDeq hD hα hαmax g hg A).1

end
end HardSphere

end OAI
