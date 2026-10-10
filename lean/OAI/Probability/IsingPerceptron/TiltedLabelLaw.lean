import Mathlib
import OAI.Probability.IsingPerceptron.VarianceDerivative

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSingletonClass I] in
lemma measurable_labeledSpinReference_general (n : ℕ) (ν : Measure I)
    [IsProbabilityMeasure ν] : Measurable (labeledSpinReference n ν) := by
  let κ : Kernel (LabeledTree n) (LabeledLeaf n) :=
    ⟨labeledLeafLaw n,measurable_labeledLeafLaw n⟩
  have : IsMarkovKernel κ := ⟨fun T => by
    change IsProbabilityMeasure (labeledLeafLaw n T)
    infer_instance⟩
  have he : (fun T => ((Kernel.const (LabeledTree n) ν).prod κ) T) =
      labeledSpinReference n ν := by
    funext T
    rw [Kernel.prod_apply,Kernel.const_apply]
    rfl
  rw [← he]
  exact ((Kernel.const (LabeledTree n) ν).prod κ).measurable

lemma measurable_cascadeCoordinateEnergy (n : ℕ) (H : I → ℝ) :
    Measurable (fun p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (I × LabeledLeaf n) =>
      cascadeCoordinateEnergy n H p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  change Measurable (fun p : LabeledTree n × (ForestVertex n → I → ℝ) =>
    H s.1+∑ i : Fin n, p.2 (edgeAt n s.2 i) s.1)
  apply measurable_const.add
  apply Finset.measurable_sum
  intro i _
  exact (measurable_pi_apply s.1).comp ((measurable_pi_apply (edgeAt n s.2 i)).comp measurable_snd)

lemma measurable_cascadeCoordinateLog (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν] (H : I → ℝ) :
    Measurable (fun p => Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
        ∂labeledSpinReference n ν p.1)) := by
  simpa only [Function.comp_def,labeledEnergyLog,← cascadeCoordinateEnergy_eq] using
    (measurable_labeledEnergyLog n ν).comp
      (show Measurable (fun p : LabeledTree n × (ForestVertex n → I → ℝ) =>
        (H,(p.1,markForestOfCoords (I → ℝ) n p.2))) from by fun_prop)

def cascadeCoordinateLog (n : ℕ) (ν : Measure I) (H : I → ℝ)
    (p : LabeledTree n × (ForestVertex n → I → ℝ)) : ℝ :=
  Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s) ∂labeledSpinReference n ν p.1)

lemma scalarCoordinate_cgf_eq_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ)
    (d : Fin n) (t : ℝ) :
    (fun p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ) =>
      cgf (fun s => cylinderField (labelLevelCoefficients n d s) p.2)
        (gibbsProbability (labeledSpinReference n ν p.1.1) (cascadeCoordinateEnergy n H p.1)) t)
      =ᵐ[(cascadeCoordinateLaw n b μ).prod gaussianCoordinates]
      (fun p => cascadeCoordinateLog n ν H
        (scalarCoordinateInsert n (fun i => if i = (d:ℕ) then t else 0) p)-cascadeCoordinateLog n ν H p.1) := by
  classical
  have hν : Measurable (fun p : LabeledTree n × (ForestVertex n → I → ℝ) => labeledSpinReference n ν p.1) :=
    (measurable_labeledSpinReference_general n ν).comp measurable_fst
  have he := random_cgf_insertion_eq (P := cascadeCoordinateLaw n b μ) hν
    (measurable_cascadeCoordinateEnergy n H) (cascadeCoordinate_exp_integrable n b hb μ ν hμ H)
    (labelLevelCoefficients n d) (labelLevelCoefficients_bound n d) t
  filter_upwards [he] with p he
  dsimp only [cascadeCoordinateLog]
  simp_rw [cascadeCoordinateEnergy_insert]
  exact he

lemma scalarCoordinate_log_difference_mean (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ)
    (a : ℕ → ℝ) :
    (∫ p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ),
      cascadeCoordinateLog n ν H (scalarCoordinateInsert n a p)-cascadeCoordinateLog n ν H p.1
      ∂(cascadeCoordinateLaw n b μ).prod gaussianCoordinates) =
      (∑ i ∈ Finset.range n, b i*a i^2)/2 := by
  let μ' : ℕ → ProbabilityMeasure (I → ℝ) := fun i => scalarShiftLaw (μ i) (NNReal.mk (a i^2) (sq_nonneg _))
  have hL := cascadeCoordinate_log_integral n b hb μ ν hμ H
  have hL' := cascadeCoordinate_log_integral n b hb μ' ν
    (fun i hi => scalarShiftLaw_exponentialNormMoments _ (hμ i hi) _) H
  have hp := scalarCoordinateInsert_preserving n b μ a
  have hi := hp.integrable_comp_of_integrable hL'.1
  have hj := hL.1.comp_fst gaussianCoordinates
  simp only [Function.comp_def] at hi
  unfold cascadeCoordinateLog
  rw [integral_sub hi hj]
  rw [integral_comp_preserving_ae hp (measurable_cascadeCoordinateLog n ν H).aestronglyMeasurable,
    integral_fun_fst (fun p => Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s) ∂labeledSpinReference n ν p.1)),probReal_univ,one_smul]
  rw [hL'.2,hL.2]
  rw [energyRecursion_scalarShift n b μ ν hμ (fun i hi => (hb.1 i hi).1)]
  simp only [NNReal.coe_mk]
  ring

lemma scalarCoordinate_cgf_mean (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ)
    (d : Fin n) {v : ℝ} (hv : 0 ≤ v) :
    (∫ p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ),
      cgf (fun s => cylinderField (labelLevelCoefficients n d s) p.2)
        (gibbsProbability (labeledSpinReference n ν p.1.1) (cascadeCoordinateEnergy n H p.1)) (Real.sqrt v)
      ∂(cascadeCoordinateLaw n b μ).prod gaussianCoordinates) = b d*v/2 := by
  classical
  rw [integral_congr_ae (scalarCoordinate_cgf_eq_ae n b hb μ ν hμ H d (Real.sqrt v)),
    scalarCoordinate_log_difference_mean n b hb μ ν hμ H]
  congr 1
  rw [Finset.sum_eq_single (d:ℕ)]
  · simp [Real.sq_sqrt hv]
  · intro i _ hi; simp [hi]
  · simp [d.isLt]

theorem cascadeCoordinate_tilted_label_tail (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) (d : Fin n) :
    (∫ p, referenceReplicaMean (labeledSpinReference n ν p.1) (cascadeCoordinateEnergy n H p)
      (fun σ : Fin 2 → I × LabeledLeaf n =>
        if (labeledAddress n (σ 1).2).take (d+1) = (labeledAddress n (σ 0).2).take (d+1)
        then 1 else 0) ∂cascadeCoordinateLaw n b μ) = 1-b d := by
  let η := fun p : LabeledTree n × (ForestVertex n → I → ℝ) =>
    gibbsProbability (labeledSpinReference n ν p.1) (cascadeCoordinateEnergy n H p)
  have hm : Measurable η := measurable_gibbsProbability
    (ν := fun p : LabeledTree n × (ForestVertex n → I → ℝ) => labeledSpinReference n ν p.1)
    ((measurable_labeledSpinReference_general n ν).comp measurable_fst)
    (measurable_cascadeCoordinateEnergy n H)
  have hd := hasDerivWithinAt_random_cylinder_variance (P := cascadeCoordinateLaw n b μ) hm
    (labelLevelCoefficients n d) (labelLevelCoefficients_bound n d) (labelLevelCoefficients_diag n d)
    (v := 0) (by norm_num)
  have hlin : HasDerivWithinAt (fun v : ℝ => b d*v/2) (b d/2) (Ici 0) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul (b d)).div_const 2).hasDerivWithinAt (s := Ici 0)
  have hde : HasDerivWithinAt (fun v : ℝ => b d*v/2)
      ((1-randomReplicaAverage (cascadeCoordinateLaw n b μ) η (labelLevelCoefficients n d) 0
        (fun σ : Fin 2 → I × LabeledLeaf n => cylinderCross
          (labelLevelCoefficients n d (σ 1)) (labelLevelCoefficients n d (σ 0))))/2) (Ici 0) 0 := by
    simp only [Real.sqrt_zero] at hd
    apply hd.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact (scalarCoordinate_cgf_mean n b hb μ ν hμ H d hv).symm
    · exact (scalarCoordinate_cgf_mean n b hb μ ν hμ H d (v := 0) (by norm_num)).symm
  have he := (hde.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ))).symm.trans
    (hlin.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ)))
  have hf := randomReplicaAverage_zero_fold (P := cascadeCoordinateLaw n b μ)
    (fun p : LabeledTree n × (ForestVertex n → I → ℝ) => labeledSpinReference n ν p.1)
    (cascadeCoordinateEnergy n H) (cascadeCoordinate_exp_integrable n b hb μ ν hμ H)
    (labelLevelCoefficients n d)
    (fun σ : Fin 2 → I × LabeledLeaf n => cylinderCross
      (labelLevelCoefficients n d (σ 1)) (labelLevelCoefficients n d (σ 0)))
  change randomReplicaAverage (cascadeCoordinateLaw n b μ) η _ _ _ = _ at hf
  rw [hf] at he
  simp only [labelLevelCoefficients_cross] at he
  linarith

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedEnergyCoords_preserving (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) :
    MeasurePreserving (fun q : ForestVertex n → Fin (EnrichedRootSize N) → ℝ =>
      fun v => enrichedIncrement N n h u (forestVertexDepth n v+1) (q v))
      (enrichedForestCoordinates N n)
      (Measure.infinitePi (fun v : ForestVertex n =>
        (enrichedIncrementLaw N n h u (forestVertexDepth n v+1) : Measure (Spin N → ℝ)))) := by
  refine ⟨Measurable.of_eval (fun v =>
    (measurable_enrichedIncrement N n h u _).comp (measurable_pi_apply v)),?_⟩
  change (Measure.infinitePi _).map _ = _
  rw [Measure.infinitePi_map_pi (f := fun v q => enrichedIncrement N n h u (forestVertexDepth n v+1) q)
    _ (fun v => measurable_enrichedIncrement N n h u _)]
  rfl

def enrichedRootLaw {A : Type*} [MeasurableSpace A] (P : Measure A) (r : ℝ≥0) (N : ℕ) :
    Measure (EnrichedPoissonRoot N A) :=
  (poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
    (Measure.infinitePi (fun _ : ℕ => P)))

instance enrichedRootLaw_probability {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (r : ℝ≥0) (N : ℕ) : IsProbabilityMeasure (enrichedRootLaw P r N) := by
  unfold enrichedRootLaw; infer_instance

def enrichedToEnergyCoords {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (p : EnrichedLabeledData N n A) : EnrichedPoissonRoot N A × (LabeledTree n × (ForestVertex n → Spin N → ℝ)) :=
  (p.1,(p.2.1,fun v => enrichedIncrement N n h u (forestVertexDepth n v+1) (p.2.2 v)))

lemma enrichedToEnergyCoords_preserving {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ) (u : Fin N → ℝ) :
    MeasurePreserving (enrichedToEnergyCoords (A := A) n h u) (enrichedCoordinateLaw P r N n b)
      ((enrichedRootLaw P r N).prod (cascadeCoordinateLaw n b (fun i => enrichedIncrementLaw N n h u (i+1)))) :=
  (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod (enrichedEnergyCoords_preserving N n h u))

lemma enrichedHamiltonian_eq_energyCoords {N : ℕ} {A : Type*}
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderData n A) :
    enrichedHamiltonian n h u φ p =
      cascadeCoordinateEnergy n (enrichedPoissonBase n h u φ (enrichedCylinderToCoordinates N n p).1)
        (enrichedToEnergyCoords n h u (enrichedCylinderToCoordinates N n p)).2 := by
  funext s
  rw [cascadeCoordinateEnergy_eq]
  exact (enrichedEnergy_eq_cylinder n h u p.2 (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i)) s.1 s.2).symm

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma measurable_cascadeCoordinateReplicaMean (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] {H : Ω → I → ℝ} (hH : Measurable H)
    {m : ℕ} (D : (Fin m → I × LabeledLeaf n) → ℝ) :
    Measurable (fun p : Ω × (LabeledTree n × (ForestVertex n → I → ℝ)) =>
      referenceReplicaMean (labeledSpinReference n ν p.2.1) (cascadeCoordinateEnergy n (H p.1) p.2) D) := by
  have hE : Measurable (fun p : (Ω × (LabeledTree n × (ForestVertex n → I → ℝ))) ×
      (I × LabeledLeaf n) => cascadeCoordinateEnergy n (H p.1.1) p.1.2 p.2) := by
    apply measurable_from_prod_countable_left
    intro s
    change Measurable (fun p : Ω × (LabeledTree n × (ForestVertex n → I → ℝ)) =>
      H p.1 s.1 + ∑ i : Fin n, p.2.2 (edgeAt n s.2 i) s.1)
    apply Measurable.add (((measurable_pi_apply s.1).comp hH).comp measurable_fst)
    exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply s.1).comp
      ((measurable_pi_apply (edgeAt n s.2 i)).comp measurable_snd.snd))
  have hD : Measurable (fun p : (Ω × (LabeledTree n × (ForestVertex n → I → ℝ))) ×
      (Fin m → I × LabeledLeaf n) => D p.2) :=
    (measurable_of_countable D).comp measurable_snd
  exact measurable_random_referenceReplicaMean
    (ν := fun p : Ω × (LabeledTree n × (ForestVertex n → I → ℝ)) => labeledSpinReference n ν p.2.1)
    ((measurable_labeledSpinReference_general n ν).comp measurable_snd.fst) hE hD

lemma cascadeCoordinate_tilted_label_tail_random (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {H : Ω → I → ℝ} (hH : Measurable H) (d : Fin n) :
    (∫ p, referenceReplicaMean (labeledSpinReference n ν p.2.1) (cascadeCoordinateEnergy n (H p.1) p.2)
      (fun σ : Fin 2 → I × LabeledLeaf n =>
        if (labeledAddress n (σ 1).2).take (d+1) = (labeledAddress n (σ 0).2).take (d+1)
        then 1 else 0) ∂P.prod (cascadeCoordinateLaw n b μ)) = 1-b d := by
  classical
  let D : (Fin 2 → I × LabeledLeaf n) → ℝ := fun σ =>
    if (labeledAddress n (σ 1).2).take (d+1) = (labeledAddress n (σ 0).2).take (d+1) then 1 else 0
  have hbD (σ) : |D σ| ≤ 1 := by dsimp only [D]; split_ifs <;> norm_num
  have hi := integrable_of_measurable_abs_le (μ := P.prod (cascadeCoordinateLaw n b μ))
    (measurable_cascadeCoordinateReplicaMean n ν hH D)
    (fun p => referenceReplicaMean_abs_le _ _ D (measurable_of_countable _) zero_le_one hbD)
  rw [integral_prod _ hi]
  calc
    _ = ∫ _ : Ω, (1-b d) ∂P := integral_congr_ae (ae_of_all _
      (fun ω => cascadeCoordinate_tilted_label_tail n b hb μ ν hμ (H ω) d))
    _ = _ := by simp

theorem enriched_tilted_label_tail {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν] {φ : A → Spin N → ℝ} (hm : Measurable φ)
    (d : Fin n) :
    enrichedReplicaAverage P r n b h u ν φ
      (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
        if (labeledAddress n (σ 1).2).take (d+1) = (labeledAddress n (σ 0).2).take (d+1)
        then 1 else 0) = 1-b d := by
  let hp := (enrichedToEnergyCoords_preserving P r n b h u).comp
    (enrichedCylinderToCoordinates_preserving P r N n b)
  have he := cascadeCoordinate_tilted_label_tail_random n b hb
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1))
    (enrichedRootLaw P r N) (measurable_enrichedPoissonBase n h u hm) d
  rw [← integral_comp_preserving_ae hp
    (measurable_cascadeCoordinateReplicaMean n ν (measurable_enrichedPoissonBase n h u hm) _).aestronglyMeasurable] at he
  unfold enrichedReplicaAverage
  convert he using 1
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  rw [enrichedHamiltonian_eq_energyCoords n h u φ p]
  rfl

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma measurable_countable_pi {Ω I X : Type*} [MeasurableSpace Ω]
    [Fintype I] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    Measurable (fun ω => Measure.pi (fun _ : I => ν ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (ω : Ω) : (Measure.pi (fun _ : I => ν ω)) s =
      ∑' x, s.indicator (fun x => (Measure.pi (fun _ : I => ν ω)) {x}) x :=
    (Measure.tsum_indicator_apply_singleton _ s hs).symm
  simp_rw [he]
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx,Measure.pi_singleton]
    exact Finset.measurable_prod _ (fun i _ =>
      (Measure.measurable_coe (measurableSet_singleton (x i))).comp hν)
  · simp only [Set.indicator_of_notMem hx]
    exact measurable_const

lemma measurable_countable_infinitePi {Ω I X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    Measurable (fun ω => Measure.infinitePi (fun _ : I => ν ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable (fun ω => (Measure.infinitePi (fun _ : I => ν ω)) s))
    (s := measurableCylinders (fun _ : I => X))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_ ?_ ?_ s hs
  · simpa only [measure_empty] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))
  · intro s hs
    obtain ⟨J,S,hS,rfl⟩ := (mem_measurableCylinders s).mp hs
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) (cylinder J S) =
        (Measure.pi (fun _ : J => ν ω)) S := by
      exact Measure.infinitePi_cylinder _ hS
    simp_rw [he]
    exact (Measure.measurable_coe hS).comp (measurable_countable_pi hν)
  · intro s hs ih
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) sᶜ =
        1-(Measure.infinitePi (fun _ : I => ν ω)) s := by rw [measure_compl hs (measure_ne_top _ _),measure_univ]
    simp_rw [he]
    exact measurable_const.sub ih
  · intro s hd hs ih
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) (⋃ n,s n) =
        ∑' n, (Measure.infinitePi (fun _ : I => ν ω)) (s n) := measure_iUnion hd hs
    simp_rw [he]
    exact Measurable.tsum ih

def replicaKernel {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] : Kernel Ω (ℕ → X) :=
  ⟨fun ω => Measure.infinitePi (fun _ : ℕ => ν ω),measurable_countable_infinitePi hν⟩

instance replicaKernel_markov {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    IsMarkovKernel (replicaKernel ν hν) := by
  constructor
  intro ω
  change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => ν ω))
  infer_instance

def replicaLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] : Measure (ℕ → X) :=
  (replicaKernel ν hν) ∘ₘ P

instance replicaLaw_probability {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    IsProbabilityMeasure (replicaLaw P ν hν) := inferInstanceAs (IsProbabilityMeasure (_ ∘ₘ P))

lemma replica_prefix_map {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (r : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ i) =
      Measure.pi (fun _ : Fin r => ν) := by
  have hi : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp (fun {i j : Fin r} h => Fin.val_injective h)).map_fun_eq_pi_map
    (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using he

lemma replicaLaw_integral_bounded {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {F : (ℕ → X) → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ σ, |F σ| ≤ C) :
    (∫ σ, F σ ∂replicaLaw P ν hν) =
      ∫ ω, ∫ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => ν ω) ∂P := by
  have hi : Integrable F (replicaLaw P ν hν) := (integrable_const C).mono'
    hF.aestronglyMeasurable (ae_of_all _ (fun σ => by simpa only [Real.norm_eq_abs] using hC σ))
  unfold replicaLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  calc
    _ = ∫ ω, ∫ σ, F σ ∂(replicaKernel ν hν) ω ∂P := by
      simpa only [Kernel.const_apply] using Kernel.integral_comp hi
    _ = _ := rfl

lemma replicaLaw_integral_prefix {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hD : ∀ σ, |D σ| ≤ C) :
    (∫ σ, D (fun i : Fin r => σ i) ∂replicaLaw P ν hν) =
      ∫ ω, ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν ω) ∂P := by
  rw [replicaLaw_integral_bounded P ν hν (F := fun σ => D (fun i : Fin r => σ i))
    ((measurable_of_countable D).comp (by fun_prop)) (fun _ => hD _)]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => ((HasLaw.mk
    ((Measurable.of_eval (fun i : Fin r => measurable_pi_apply (i : ℕ))).aemeasurable)
    (replica_prefix_map (ν ω) r)).integral_comp (measurable_of_countable D).aestronglyMeasurable))

abbrev JointEntry := Set.Icc (-1 : ℝ) 1 × Set.Icc (0 : ℝ) 1
abbrev JointArray := ℕ × ℕ → JointEntry

def sampledOverlapArray {X : Type*} (κ : X → X → JointEntry) (σ : ℕ → X) : JointArray :=
  fun ij => κ (σ ij.1) (σ ij.2)

lemma measurable_sampledOverlapArray {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (κ : X → X → JointEntry) :
    Measurable (sampledOverlapArray κ) := by
  apply Measurable.of_eval
  intro ij
  change Measurable (fun σ : ℕ → X => κ (σ ij.1) (σ ij.2))
  have hk : Measurable (fun xx : X × X => κ xx.1 xx.2) := measurable_of_countable _
  have hp : Measurable (fun σ : ℕ → X => (σ ij.1,σ ij.2)) :=
    (measurable_pi_apply ij.1).prodMk (measurable_pi_apply ij.2)
  exact hk.comp hp

def overlapArrayLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (κ : X → X → JointEntry) : ProbabilityMeasure JointArray :=
  ⟨(replicaLaw P ν hν).map (sampledOverlapArray κ),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_sampledOverlapArray κ).aemeasurable).mpr inferInstance⟩

theorem jointArrayLaw_subsequence (L : ℕ → ProbabilityMeasure JointArray) :
    ∃ μ : ProbabilityMeasure JointArray, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (L ∘ φ) atTop (𝓝 μ) := by
  obtain ⟨μ,_,φ,hφ,ht⟩ := isSeqCompact_univ.subseq_of_frequently_in
    (x := L) (Filter.Frequently.of_forall (fun _ => Set.mem_univ _))
  exact ⟨μ,φ,hφ,ht⟩

lemma jointArray_tendsto_integral {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    {F : JointArray → ℝ} (hF : Continuous F) :
    Tendsto (fun N => ∫ x, F x ∂(L N : Measure JointArray)) atTop
      (𝓝 (∫ x, F x ∂(μ : Measure JointArray))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩)

abbrev JointBlock (n : ℕ) := Fin n → Fin n → JointEntry

def entryCoordinate (b : Bool) (x : JointEntry) : ℝ := if b then x.2.1 else x.1.1

lemma continuous_entryCoordinate (b : Bool) : Continuous (entryCoordinate b) := by
  cases b
  · exact continuous_subtype_val.comp continuous_fst
  · exact continuous_subtype_val.comp continuous_snd

lemma entryCoordinate_ext (x y : JointEntry)
    (h : ∀ b, entryCoordinate b x = entryCoordinate b y) : x = y := by
  apply Prod.ext
  · exact Subtype.ext (h false)
  · exact Subtype.ext (h true)

def blockPairCoordinate (n : ℕ) (i : ((Fin n × Fin n) × Bool) ⊕ Bool)
    (x : JointBlock n × JointEntry) : ℝ :=
  match i with
  | .inl ijb => entryCoordinate ijb.2 (x.1 ijb.1.1 ijb.1.2)
  | .inr b => entryCoordinate b x.2

lemma continuous_blockPairCoordinate (n : ℕ) (i : ((Fin n × Fin n) × Bool) ⊕ Bool) :
    Continuous (blockPairCoordinate n i) := by
  cases i with
  | inl ijb => exact (continuous_entryCoordinate ijb.2).comp (by fun_prop)
  | inr b => exact (continuous_entryCoordinate b).comp continuous_snd

lemma blockPairCoordinate_ext (n : ℕ) (x y : JointBlock n × JointEntry)
    (h : ∀ i, blockPairCoordinate n i x = blockPairCoordinate n i y) : x = y := by
  apply Prod.ext
  · funext i j
    apply entryCoordinate_ext
    intro b
    exact h (.inl ((i,j),b))
  · apply entryCoordinate_ext
    intro b
    exact h (.inr b)

theorem block_pair_monomials_unique (n : ℕ)
    (P Q : Measure (JointBlock n × JointEntry)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ (D : JointBlock n → ℝ), Continuous D → ∀ p d : ℕ,
      (∫ x, D x.1 * x.2.1.1 ^ p * x.2.2.1 ^ d ∂P) =
        ∫ x, D x.1 * x.2.1.1 ^ p * x.2.2.1 ^ d ∂Q) : P = Q := by
  classical
  have : TopologicalSpace.SeparableSpace (JointBlock n × JointEntry) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (JointBlock n × JointEntry) := inferInstance
  let I := ((Fin n × Fin n) × Bool) ⊕ Bool
  let g : I → ((JointBlock n × JointEntry) →ᵇ ℝ) := fun i =>
    BoundedContinuousFunction.mkOfCompact ⟨blockPairCoordinate n i,continuous_blockPairCoordinate n i⟩
  let ev : MvPolynomial I ℝ →ₐ[ℝ] ((JointBlock n × JointEntry) →ᵇ ℝ) := MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((JointBlock n × JointEntry) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : I) (x : JointBlock n × JointEntry) : g i x = blockPairCoordinate n i x := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i,hi⟩ : ∃ i : I, blockPairCoordinate n i x ≠ blockPairCoordinate n i y := by
      by_contra! hno
      exact hxy (blockPairCoordinate_ext n x y hno)
    refine ⟨g i,?_,?_⟩
    · refine ⟨(g i).toContinuousMap,?_,rfl⟩
      exact ⟨g i,⟨MvPolynomial.X i,by simp [ev]⟩,rfl⟩
    · simpa only [hap] using hi
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p,rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add,BoundedContinuousFunction.coe_add,Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    let D : JointBlock n → ℝ := fun b => ∏ i : (Fin n × Fin n) × Bool,
      entryCoordinate i.2 (b i.1.1 i.1.2) ^ k (.inl i)
    have hD : Continuous D := by
      apply continuous_finsetProd
      intro i _
      exact ((continuous_entryCoordinate i.2).comp (by fun_prop)).pow _
    have he (x : JointBlock n × JointEntry) : ev (MvPolynomial.monomial k c) x =
        c*(D x.1 * x.2.1.1 ^ k (.inr false) * x.2.2.1 ^ k (.inr true)) := by
      simp only [ev,MvPolynomial.aeval_monomial]
      rw [Finsupp.prod_pow]
      simp only [BoundedContinuousFunction.coe_mul,Pi.mul_apply,
        BoundedContinuousFunction.coe_prod,BoundedContinuousFunction.coe_pow,
        BoundedContinuousFunction.algebraMap_apply,Finset.prod_apply,Pi.pow_apply,smul_eq_mul,mul_one]
      change c*(∏ i : I,g i x ^ k i) = _
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_bool,hap,blockPairCoordinate,entryCoordinate,Bool.false_eq_true,ite_false,ite_true]
      dsimp only [D,entryCoordinate]
      ring
    change (∫ x, ev (MvPolynomial.monomial k c) x ∂P) = ∫ x, ev (MvPolynomial.monomial k c) x ∂Q
    simp only [he,integral_const_mul]
    exact congrArg (c * ·) (h D hD _ _)

def jointBlockView (n : ℕ) (x : JointArray) : JointBlock n := fun i j => x (i,j)

def jointBlockLink (n i j : ℕ) (x : JointArray) : JointBlock n × JointEntry :=
  (jointBlockView n x,x (i,j))

lemma continuous_jointBlockView (n : ℕ) : Continuous (jointBlockView n) := by
  unfold jointBlockView
  fun_prop

lemma continuous_jointBlockLink (n i j : ℕ) : Continuous (jointBlockLink n i j) := by
  unfold jointBlockLink
  exact (continuous_jointBlockView n).prodMk (continuous_apply _)

lemma compact_integrable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {P : Measure X} [IsFiniteMeasure P]
    {F : X → ℝ} (hF : Continuous F) : Integrable F P :=
  (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩).integrable P

def HasEntryGhirlandaGuerra {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (B : Ω → ℕ → ℕ → E) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n)
    (A : Set (Fin n → Fin n → E)), MeasurableSet A →
    ∀ (t : Set E), MeasurableSet t →
    μ.real ({ω | (fun j k : Fin n => B ω j k) ∈ A} ∩ {ω | B ω i n ∈ t}) =
      (μ.real {ω | (fun j k : Fin n => B ω j k) ∈ A} * μ.real {ω | B ω 0 1 ∈ t}) / n +
      (∑ j ∈ Finset.univ.erase i,
        μ.real ({ω | (fun j k : Fin n => B ω j k) ∈ A} ∩ {ω | B ω i j ∈ t})) / n

theorem joint_monomial_measure_identity (μ : Measure JointArray) [IsProbabilityMeasure μ]
    (n : ℕ) (i : Fin n)
    (h : ∀ (D : JointBlock n → ℝ), Continuous D → ∀ p d : ℕ,
      (n : ℝ)*(∫ x, D (jointBlockView n x)*(x (i,n)).1.1^p*(x (i,n)).2.1^d ∂μ) =
        (∫ x, D (jointBlockView n x) ∂μ)*(∫ x, (x (0,1)).1.1^p*(x (0,1)).2.1^d ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d ∂μ) :
    (n : ℝ≥0∞) • μ.map (jointBlockLink n i n) =
      (μ.map (jointBlockView n)).prod (μ.map (fun x => x (0,1))) +
        ∑ j ∈ Finset.univ.erase i, μ.map (jointBlockLink n i j) := by
  classical
  let block := μ.map (jointBlockView n)
  let pair := μ.map (fun x => x (0,1))
  let link := fun j : ℕ => μ.map (jointBlockLink n i j)
  have : IsProbabilityMeasure block := (Measure.isProbabilityMeasure_map_iff
    (continuous_jointBlockView n).measurable.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure pair := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply (0,1)).aemeasurable).mpr inferInstance
  have (j : ℕ) : IsProbabilityMeasure (link j) := (Measure.isProbabilityMeasure_map_iff
    (continuous_jointBlockLink n i j).measurable.aemeasurable).mpr inferInstance
  change (n : ℝ≥0∞) • link n = block.prod pair+∑ j ∈ Finset.univ.erase i, link j
  have : IsFiniteMeasure ((n : ℝ≥0∞) • link n) := (link n).smul_finite (by simp)
  apply block_pair_monomials_unique n
  intro D hD p d
  let F : JointBlock n × JointEntry → ℝ := fun x => D x.1*x.2.1.1^p*x.2.2.1^d
  have hF : Continuous F := by fun_prop
  have hi (j : ℕ) : (∫ x, F x ∂link j) =
      ∫ x, D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d ∂μ := by
    exact integral_map (continuous_jointBlockLink n i j).measurable.aemeasurable hF.aestronglyMeasurable
  change (∫ x, F x ∂(n : ℝ≥0∞) • link n) =
    ∫ x, F x ∂(block.prod pair+∑ j ∈ Finset.univ.erase i, link j)
  rw [integral_smul_measure,ENNReal.toReal_natCast,smul_eq_mul,
    integral_add_measure (compact_integrable hF) (compact_integrable hF),
    integral_finsetSum_measure (fun j _ => compact_integrable hF),hi]
  simp_rw [hi]
  rw [h D hD]
  congr 1
  have hp : Continuous (fun x : JointEntry => x.1.1^p*x.2.1^d) := by fun_prop
  have he : (∫ x, F x ∂block.prod pair) =
      (∫ b, D b ∂block)*(∫ x, x.1.1^p*x.2.1^d ∂pair) := by
    simpa only [F,mul_assoc] using
      (integral_prod_mul (μ := block) (ν := pair) D (fun x : JointEntry => x.1.1^p*x.2.1^d))
  rw [he,integral_map (continuous_jointBlockView n).measurable.aemeasurable hD.aestronglyMeasurable,
    integral_map (measurable_pi_apply (0,1)).aemeasurable hp.aestronglyMeasurable]

theorem joint_monomialGG_measurable (μ : Measure JointArray) [IsProbabilityMeasure μ]
    (h : ∀ n, 2 ≤ n → ∀ i : Fin n,
      ∀ (D : JointBlock n → ℝ), Continuous D → ∀ p d : ℕ,
      (n : ℝ)*(∫ x, D (jointBlockView n x)*(x (i,n)).1.1^p*(x (i,n)).2.1^d ∂μ) =
        (∫ x, D (jointBlockView n x) ∂μ)*(∫ x, (x (0,1)).1.1^p*(x (0,1)).2.1^d ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d ∂μ) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) μ := by
  classical
  intro n hn i A hA t ht
  have he := congrArg (fun ν : Measure (JointBlock n × JointEntry) => (ν (A ×ˢ t)).toReal)
    (joint_monomial_measure_identity μ n i (h n hn i))
  have hmap : ∀ j : ℕ, Measurable (jointBlockLink n i j) := fun j =>
    (continuous_jointBlockLink n i j).measurable
  have hblock := (continuous_jointBlockView n).measurable
  have hpair : Measurable (fun x : JointArray => x (0,1)) := by fun_prop
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    Measure.add_apply,Measure.prod_prod,Measure.finsetSum_apply,
    Measure.map_apply (hmap _) (hA.prod ht),Measure.map_apply hblock hA,Measure.map_apply hpair ht] at he
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top _ _)),ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)] at he
  change (n : ℝ)*μ.real ({x | jointBlockView n x ∈ A} ∩ {x | x (i,n) ∈ t}) =
    μ.real {x | jointBlockView n x ∈ A}*μ.real {x | x (0,1) ∈ t}+
    ∑ j ∈ Finset.univ.erase i, μ.real ({x | jointBlockView n x ∈ A} ∩ {x | x (i,j) ∈ t}) at he
  change μ.real ({x | jointBlockView n x ∈ A} ∩ {x | x (i,n) ∈ t}) =
    (μ.real {x | jointBlockView n x ∈ A}*μ.real {x | x (0,1) ∈ t})/n+
    (∑ j ∈ Finset.univ.erase i, μ.real ({x | jointBlockView n x ∈ A} ∩ {x | x (i,j) ∈ t}))/n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0]
  nlinarith [he]

end IsingPerceptron

end

end OAI
