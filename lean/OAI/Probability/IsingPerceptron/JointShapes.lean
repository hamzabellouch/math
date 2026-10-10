import Mathlib
import OAI.Probability.IsingPerceptron.ArraySynchronization
import OAI.Probability.IsingPerceptron.EnrichedGGFinite
import OAI.Probability.IsingPerceptron.SamplingIndependent

namespace OAI

/-! Joint Shapes. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma retained_joint_shape_ae (n r : ℕ) (b a : ℕ → ℝ) :
    ∀ᵐ p ∂retainedLabelJoint n b a, pathPrefixPattern n r (sampledMarkPath n p) =
      labelPrefixPattern n r (fun i => p.2 i) := by
  have hg : ∀ᵐ p ∂retainedLabelBase n b, Function.Injective p.2 := by
    have hp := measurePreserving_snd (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
      (ν := Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1))
    exact hp.quasiMeasurePreserving.tendsto_ae.eventually (gaussian_marks_injective n (fun _ => 0))
  have hf : MeasurePreserving Prod.fst (retainedLabelJoint n b a) (retainedLabelBase n b) :=
    ⟨measurable_fst,Measure.fst_compProd _ _⟩
  have hh := hf.quasiMeasurePreserving.tendsto_ae.eventually hg
  filter_upwards [hh] with p hp
  exact pathPrefixPattern_coordinates n r p.2 p.1.2 hp

lemma measurable_sampledLabelPattern (n r : ℕ) :
    Measurable (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
      labelPrefixPattern n r (fun i => p.2 i)) :=
  (measurable_infiniteLabelPattern n r).comp measurable_snd

theorem retained_joint_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (a : ℕ → ℝ) (D : PrefixPattern n r → ℝ) :
    (∫ p, D (labelPrefixPattern n r (fun i => p.2 i)) ∂retainedLabelJoint n b a) =
      ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b := by
  have hF : Measurable (fun z => D (pathPrefixPattern n r z)) :=
    (measurable_of_countable D).comp (measurable_pathPrefixPattern n r)
  calc
    _ = ∫ p, D (pathPrefixPattern n r (sampledMarkPath n p)) ∂retainedLabelJoint n b a := by
      apply integral_congr_ae
      filter_upwards [retained_joint_shape_ae n r b a] with p hp
      rw [hp]
    _ = ∫ z, D (pathPrefixPattern n r z) ∂gaussianMarkedPathLaw n b (fun i => b i*a i) := by
      rw [← integral_map (measurable_sampledMarkPath n).aemeasurable hF.aestronglyMeasurable,
        retained_joint_path_law n b hb a]
      rfl
    _ = _ := gaussian_marked_shape n r b hb _ D

theorem retained_joint_shape_score (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (a : ℕ → ℝ) (d : Fin n) (D : PrefixPattern n r → ℝ) :
    (∫ p, D (labelPrefixPattern n r (fun i => p.2 i))*p.1.2 (edgeAt n (p.2 0) d)
      ∂retainedLabelJoint n b a) =
      (∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b)*(b d*a d) := by
  have hF : Measurable (fun z : ℕ → Fin n → ℝ => D (pathPrefixPattern n r z)*z 0 d) :=
    ((measurable_of_countable D).comp (measurable_pathPrefixPattern n r)).mul
      ((measurable_pi_apply d).comp (measurable_pi_apply 0))
  calc
    _ = ∫ p, D (pathPrefixPattern n r (sampledMarkPath n p))*sampledMarkPath n p 0 d
        ∂retainedLabelJoint n b a := by
      apply integral_congr_ae
      filter_upwards [retained_joint_shape_ae n r b a] with p hp
      rw [hp]; rfl
    _ = ∫ z, D (pathPrefixPattern n r z)*z 0 d ∂gaussianMarkedPathLaw n b (fun i => b i*a i) := by
      rw [← integral_map (measurable_sampledMarkPath n).aemeasurable hF.aestronglyMeasurable,
        retained_joint_path_law n b hb a]
      rfl
    _ = _ := gaussian_marked_shape_score n r b hb _ d D

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPattern_bound (n r : ℕ) (D : PrefixPattern n r → ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |D x| ≤ c := by
  refine ⟨∑ x, |D x|,Finset.sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  intro x
  exact Finset.single_le_sum (f := fun x => |D x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)

lemma retained_joint_shape_score_integrable (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (a : ℕ → ℝ) (d : Fin n) (D : PrefixPattern n r → ℝ) :
    Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))*p.1.2 (edgeAt n (p.2 0) d))
      (retainedLabelJoint n b a) := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n r D
  have hi := gaussian_marked_shape_score_integrable n r b hb (fun i => b i*a i) d D hD
  have hF : Measurable (fun z : ℕ → Fin n → ℝ => D (pathPrefixPattern n r z)*z 0 d) :=
    ((measurable_of_countable D).comp (measurable_pathPrefixPattern n r)).mul
      ((measurable_pi_apply d).comp (measurable_pi_apply 0))
  change Integrable _ ((markedReplicaLaw n b (fun i => ⟨gaussianReal (b i*a i) 1,inferInstance⟩)).map (replicaMarkPath n)) at hi
  rw [← retained_joint_path_law n b hb a] at hi
  have hj := (integrable_map_measure hF.aestronglyMeasurable (measurable_sampledMarkPath n).aemeasurable).mp hi
  apply hj.congr
  filter_upwards [retained_joint_shape_ae n r b a] with p hp
  change D (pathPrefixPattern n r (sampledMarkPath n p))*sampledMarkPath n p 0 d = _
  rw [hp]; rfl

lemma raw_joint_shape_score_integrable (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))*
      cylinderField (leafLevelCoefficients n d (p.2 0)) p.1.2) (rawLabelJoint n b d t) := by
  have hi := retained_joint_shape_score_integrable n r b hb (fun i => if i = d then t else 0) d D
  have hp := raw_retained_joint_preserving n b d t
  have hi' : Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))*p.1.2 (edgeAt n (p.2 0) d))
      ((rawLabelJoint n b d t).map (rawLabelToRetained n)) := by rwa [hp.map_eq]
  have hj := (integrable_map_measure hi'.aestronglyMeasurable hp.measurable.aemeasurable).mp hi'
  change Integrable (fun p : (LabeledTree n × (ℕ → ℝ)) × (ℕ → LabeledLeaf n) => D (labelPrefixPattern n r (fun i => p.2 i))*edgeGaussianCoordinates n p.1.2 (edgeAt n (p.2 0) d)) _ at hj
  simpa only [leafLevelCoefficients_field] using hj

lemma raw_joint_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    (∫ p, D (labelPrefixPattern n r (fun i => p.2 i)) ∂rawLabelJoint n b d t) =
      ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b := by
  have hF : Measurable (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
      D (labelPrefixPattern n r (fun i => p.2 i))) :=
    (measurable_of_countable D).comp (measurable_sampledLabelPattern n r)
  have h := (HasLaw.mk (raw_retained_joint_preserving n b d t).measurable.aemeasurable (raw_retained_joint_preserving n b d t).map_eq).integral_comp hF.aestronglyMeasurable
  exact h.trans (retained_joint_shape n r b hb _ D)

lemma raw_joint_shape_score (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    (∫ p, D (labelPrefixPattern n r (fun i => p.2 i))*
      cylinderField (leafLevelCoefficients n d (p.2 0)) p.1.2 ∂rawLabelJoint n b d t) =
      (∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b)*(b d*t) := by
  have hi := retained_joint_shape_score_integrable n r b hb (fun i => if i = d then t else 0) d D
  have h := (HasLaw.mk (raw_retained_joint_preserving n b d t).measurable.aemeasurable (raw_retained_joint_preserving n b d t).map_eq).integral_comp hi.aestronglyMeasurable
  have hh := h.trans (retained_joint_shape_score n r b hb (fun i => if i = d then t else 0) d D)
  simpa only [Function.comp_apply,rawLabelToRetained,leafLevelCoefficients_field,ite_eq_left rfl,ite_true] using hh

lemma randomReplicaAverage_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    randomReplicaAverage (labeledCascadeLaw n b) (labeledLeafLaw n) (leafLevelCoefficients n d) t
      (fun σ => D (labelPrefixPattern n r σ)) =
      ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n r D
  have hi : Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))) (rawLabelJoint n b d t) :=
    integrable_of_measurable_abs_le
      ((measurable_of_countable (fun σ : Fin r → LabeledLeaf n => D (labelPrefixPattern n r σ))).comp (by fun_prop))
      (fun _ => hD _)
  exact (rawJoint_integral_reference n b d t r (fun _ σ => D (labelPrefixPattern n r σ)) hi).symm.trans
    (raw_joint_shape n r b hb d t D)

lemma randomReplicaEnergy_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n (r+1) → ℝ) :
    randomReplicaEnergy (labeledCascadeLaw n b) (labeledLeafLaw n) (leafLevelCoefficients n d) t
      (fun σ => D (labelPrefixPattern n (r+1) σ)) =
      (∫ σ, D (labelPrefixPattern n (r+1) (fun i => σ i)) ∂cascadeReplicaLaw n b)*(b d*t) := by
  have hi := raw_joint_shape_score_integrable n (r+1) b hb d t D
  have h := rawJoint_integral_reference n b d t (r+1)
    (fun p σ => D (labelPrefixPattern n (r+1) σ)*cylinderField (leafLevelCoefficients n d (σ 0)) p.2) hi
  simpa only [randomReplicaEnergy,rawLabelBase,mul_comm] using h.symm.trans (raw_joint_shape_score n (r+1) b hb d t D)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def prefixPatternMean (n r : ℕ) (b : ℕ → ℝ) (D : PrefixPattern n r → ℝ) : ℝ :=
  ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b

def patternReindex {n r s : ℕ} (Q : PrefixPattern n r) (e : Fin s → Fin r) : PrefixPattern n s :=
  fun i j d => Q (e i) (e j) d

def boolReal (b : Bool) : ℝ := if b then 1 else 0

lemma patternReindex_label {n r s : ℕ} (σ : Fin r → LabeledLeaf n) (e : Fin s → Fin r) :
    patternReindex (labelPrefixPattern n r σ) e = labelPrefixPattern n s (σ ∘ e) := rfl

lemma leafLevelCoefficients_cross_bool (n r : ℕ) (d : Fin n) (σ : Fin r → LabeledLeaf n) (i j : Fin r) :
    cylinderCross (leafLevelCoefficients n d (σ i)) (leafLevelCoefficients n d (σ j)) =
      boolReal (labelPrefixPattern n r σ i j d) := by
  rw [leafLevelCoefficients_cross]
  simp only [labelPrefixPattern,boolReal]
  split <;> simp

lemma prefixPatternMean_const (n r : ℕ) (b : ℕ → ℝ) (c : ℝ) :
    prefixPatternMean n r b (fun _ => c) = c := by simp [prefixPatternMean]

 
theorem cascade_prefix_gg (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (D : PrefixPattern n (r+1) → ℝ) :
    (r+1 : ℕ)*prefixPatternMean n (r+1+1) b
      (fun Q => D (patternReindex Q Fin.succ)*boolReal (Q 1 0 d)) =
      (1-b d)*prefixPatternMean n (r+1) b D +
      prefixPatternMean n (r+1) b (fun Q => D Q*(∑ j : Fin r, boolReal (Q 0 j.succ d))) := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n (r+1) D
  have h := randomReplicaEnergy_identity (P := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (measurable_labeledLeafLaw n) (leafLevelCoefficients n d) (leafLevelCoefficients_bound n d)
    (leafLevelCoefficients_diag n d) 1 (fun σ => D (labelPrefixPattern n (r+1) σ)) hc (fun σ => hD _)
  have hE : (fun σ : Fin (r+1) → LabeledLeaf n => D (labelPrefixPattern n (r+1) σ)*
      (∑ l : Fin r, cylinderCross (leafLevelCoefficients n d (σ 0)) (leafLevelCoefficients n d (σ l.succ)))) =
      (fun σ => (fun Q : PrefixPattern n (r+1) => D Q*(∑ l : Fin r, boolReal (Q 0 l.succ d)))
        (labelPrefixPattern n (r+1) σ)) := by
    funext σ
    simp only [leafLevelCoefficients_cross_bool]
  have hF : (fun τ : Fin (r+1+1) → LabeledLeaf n => D (labelPrefixPattern n (r+1) (Fin.tail τ))*
      cylinderCross (leafLevelCoefficients n d ((Fin.tail τ) 0)) (leafLevelCoefficients n d (τ 0))) =
      (fun τ => (fun Q : PrefixPattern n (r+1+1) => D (patternReindex Q Fin.succ)*boolReal (Q 1 0 d))
        (labelPrefixPattern n (r+1+1) τ)) := by
    funext τ
    change D (labelPrefixPattern n (r+1) (Fin.tail τ))*cylinderCross (leafLevelCoefficients n d (τ 1)) (leafLevelCoefficients n d (τ 0)) = _
    rw [leafLevelCoefficients_cross_bool n (r+1+1) d τ 1 0]
    rfl
  rw [hE,hF,randomReplicaEnergy_shape n r b hb d 1 D,
    randomReplicaAverage_shape n (r+1) b hb d 1 D,
    randomReplicaAverage_shape n (r+1) b hb d 1 (fun Q => D Q*(∑ l : Fin r, boolReal (Q 0 l.succ d))),
    randomReplicaAverage_shape n (r+1+1) b hb d 1 (fun Q => D (patternReindex Q Fin.succ)*boolReal (Q 1 0 d))] at h
  change prefixPatternMean n (r+1) b D*(b d*1) = _ at h
  change _ = (1-b d)*prefixPatternMean n (r+1) b D+_ 
  dsimp only [prefixPatternMean] at *
  linarith

lemma prefix_pair_mean (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (d : Fin n) :
    prefixPatternMean n 2 b (fun Q => boolReal (Q 1 0 d)) = 1-b d := by
  have h := cascade_prefix_gg n 0 b hb d (fun _ => 1)
  simpa only [Nat.zero_add,Nat.cast_one,one_mul,Fin.sum_univ_zero,mul_zero,
    prefixPatternMean_const,mul_one,add_zero] using h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma replica_injective_map_reindex {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {r : ℕ} {e : Fin r → ℕ} (he : Function.Injective e) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ (e i)) =
      Measure.pi (fun _ : Fin r => ν) := by
  have hi : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have h := (hi.precomp (fun {_ _} h => he h)).map_fun_eq_pi_map
    (fun _ => (measurable_pi_apply _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using h

lemma replicaLaw_integral_injective_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} {e : Fin r → ℕ} (he : Function.Injective e)
    (F : (Fin r → X) → ℝ) {c : ℝ} (hF : ∀ σ, |F σ| ≤ c) :
    (∫ σ, F (fun i => σ (e i)) ∂replicaLaw P ν hν) =
      ∫ σ, F (fun i => σ i) ∂replicaLaw P ν hν := by
  have h1m : Measurable (fun σ : ℕ → X => F (fun i => σ (e i))) :=
    (measurable_of_countable F).comp (by fun_prop)
  have h2m : Measurable (fun σ : ℕ → X => F (fun i : Fin r => σ i)) :=
    (measurable_of_countable F).comp (by fun_prop)
  rw [replicaLaw_integral_bounded P ν hν h1m (fun σ => hF _),
    replicaLaw_integral_bounded P ν hν h2m (fun σ => hF _)]
  apply integral_congr_ae
  filter_upwards [] with ω
  have h1 : HasLaw (fun σ : ℕ → X => fun i : Fin r => σ (e i))
      (Measure.pi (fun _ : Fin r => ν ω)) (Measure.infinitePi (fun _ : ℕ => ν ω)) :=
    ⟨(by fun_prop : Measurable _).aemeasurable,replica_injective_map_reindex (ν ω) he⟩
  have h2 : HasLaw (fun σ : ℕ → X => fun i : Fin r => σ i)
      (Measure.pi (fun _ : Fin r => ν ω)) (Measure.infinitePi (fun _ : ℕ => ν ω)) :=
    ⟨(by fun_prop : Measurable _).aemeasurable,replica_prefix_map (ν ω) r⟩
  exact (h1.integral_comp (measurable_of_countable F).aestronglyMeasurable).trans
    (h2.integral_comp (measurable_of_countable F).aestronglyMeasurable).symm

lemma cascadeReplicaLaw_eq_replicaLaw (n : ℕ) (b : ℕ → ℝ) :
    cascadeReplicaLaw n b = replicaLaw (labeledCascadeLaw n b) (labeledLeafLaw n) (measurable_labeledLeafLaw n) := by
  unfold cascadeReplicaLaw replicaLaw
  congr 1

lemma cascade_integral_injective (n : ℕ) (b : ℕ → ℝ) {r : ℕ} {e : Fin r → ℕ}
    (he : Function.Injective e) (F : (Fin r → LabeledLeaf n) → ℝ) {c : ℝ} (hF : ∀ σ, |F σ| ≤ c) :
    (∫ σ, F (fun i => σ (e i)) ∂cascadeReplicaLaw n b) =
      ∫ σ, F (fun i => σ i) ∂cascadeReplicaLaw n b := by
  simp only [cascadeReplicaLaw_eq_replicaLaw]
  exact replicaLaw_integral_injective_eq (Ω := LabeledTree n) (X := LabeledLeaf n)
    (labeledCascadeLaw n b) (labeledLeafLaw n) (measurable_labeledLeafLaw n) (r := r) (e := e) he F hF

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPatternMean_injective (n r : ℕ) (b : ℕ → ℝ) {e : Fin r → ℕ}
    (he : Function.Injective e) (D : PrefixPattern n r → ℝ) :
    (∫ σ, D (labelPrefixPattern n r (fun i => σ (e i))) ∂cascadeReplicaLaw n b) =
      prefixPatternMean n r b D := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n r D
  exact cascade_integral_injective n b he (fun τ => D (labelPrefixPattern n r τ)) (fun σ => hD _)

lemma prefixPatternMean_congr (n r : ℕ) (b : ℕ → ℝ) {D E : PrefixPattern n r → ℝ}
    (h : ∀ σ : Fin r → LabeledLeaf n, D (labelPrefixPattern n r σ) = E (labelPrefixPattern n r σ)) :
    prefixPatternMean n r b D = prefixPatternMean n r b E :=
  integral_congr_ae (ae_of_all _ (fun σ => h (fun index => σ index)))

lemma prefixPatternMean_integrable (n r : ℕ) (b : ℕ → ℝ) (D : PrefixPattern n r → ℝ) :
    Integrable (fun σ => D (labelPrefixPattern n r (fun i => σ i))) (cascadeReplicaLaw n b) := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n r D
  exact integrable_of_measurable_abs_le
    ((measurable_of_countable D).comp (measurable_infiniteLabelPattern n r)) (fun σ => hD _)

lemma prefixPatternMean_add (n r : ℕ) (b : ℕ → ℝ) (D E : PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => D Q+E Q) = prefixPatternMean n r b D+prefixPatternMean n r b E :=
  integral_add (prefixPatternMean_integrable n r b D) (prefixPatternMean_integrable n r b E)

lemma prefixPatternMean_sub (n r : ℕ) (b : ℕ → ℝ) (D E : PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => D Q-E Q) = prefixPatternMean n r b D-prefixPatternMean n r b E :=
  integral_sub (prefixPatternMean_integrable n r b D) (prefixPatternMean_integrable n r b E)

lemma prefixPatternMean_mul (n r : ℕ) (b : ℕ → ℝ) (c : ℝ) (D : PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => c*D Q) = c*prefixPatternMean n r b D := integral_const_mul _ _

lemma prefixPatternMean_sum {I : Type*} (s : Finset I) (n r : ℕ) (b : ℕ → ℝ) (D : I → PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => ∑ i ∈ s, D i Q) = ∑ i ∈ s, prefixPatternMean n r b (D i) :=
  integral_finsetSum s (fun i _ => prefixPatternMean_integrable n r b (D i))

def lastToFront (r : ℕ) : Fin (r+1+1) → ℕ := Fin.cases (r+1) Fin.val

lemma lastToFront_injective (r : ℕ) : Function.Injective (lastToFront r) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · intro _; rfl
  · simp only [lastToFront,Fin.cases_zero,Fin.cases_succ]; intro h; have := j.isLt; omega
  · simp only [lastToFront,Fin.cases_zero,Fin.cases_succ]; intro h; have := i.isLt; omega
  · simp only [lastToFront,Fin.cases_succ]; intro h; exact congrArg Fin.succ (Fin.ext h)

lemma prefix_fresh_reindex (n r : ℕ) (b : ℕ → ℝ) (d : Fin n)
    (D : PrefixPattern n (r+1) → ℝ) :
    prefixPatternMean n (r+1+1) b (fun Q => D (patternReindex Q Fin.succ)*boolReal (Q 1 0 d)) =
      prefixPatternMean n (r+1+1) b
        (fun Q => D (patternReindex Q Fin.castSucc)*boolReal (Q 0 (Fin.last (r+1)) d)) := by
  have h := prefixPatternMean_injective n (r+1+1) b (lastToFront_injective r)
    (fun Q => D (patternReindex Q Fin.succ)*boolReal (Q 1 0 d))
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with σ
  rfl

lemma cascade_prefix_gg_first (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (D : PrefixPattern n (r+1) → ℝ) :
    (r+1 : ℕ)*prefixPatternMean n (r+1+1) b
      (fun Q => D (patternReindex Q Fin.castSucc)*boolReal (Q 0 (Fin.last (r+1)) d)) =
      (1-b d)*prefixPatternMean n (r+1) b D +
      prefixPatternMean n (r+1) b (fun Q => D Q*(∑ j : Fin r, boolReal (Q 0 j.succ d))) := by
  rw [← prefix_fresh_reindex]
  exact cascade_prefix_gg n r b hb d D

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPatternMean_perm (n r : ℕ) (b : ℕ → ℝ) (e : Equiv.Perm (Fin r))
    (D : PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => D (patternReindex Q e)) = prefixPatternMean n r b D := by
  have h := prefixPatternMean_injective n r b (e := fun i => (e i).val)
    (fun _ _ h => e.injective (Fin.ext h)) D
  exact h

lemma patternReindex_perm_cancel {n r : ℕ} (Q : PrefixPattern n r) (e : Equiv.Perm (Fin r)) :
    patternReindex (patternReindex Q e) e.symm = Q := by
  funext i j d
  simp [patternReindex]

lemma prefix_fresh_permuted (n r : ℕ) (b : ℕ → ℝ) (d : Fin n)
    (e : Equiv.Perm (Fin (r+1))) (D : PrefixPattern n (r+1) → ℝ) :
    prefixPatternMean n (r+1+1) b (fun Q => D (patternReindex (patternReindex Q Fin.succ) e.symm)*boolReal (Q 1 0 d)) =
      prefixPatternMean n (r+1+1) b
        (fun Q => D (patternReindex Q Fin.castSucc)*boolReal (Q (e 0).castSucc (Fin.last (r+1)) d)) := by
  have h := prefixPatternMean_injective n (r+1+1) b (newReplicaEmbedding_injective (r+1) e)
    (fun Q => D (patternReindex (patternReindex Q Fin.succ) e.symm)*boolReal (Q 1 0 d))
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with σ
  congr 1
  · apply congrArg D
    funext i j d
    simp [patternReindex,labelPrefixPattern,newReplicaEmbedding]

lemma prefix_old_permuted (n r : ℕ) (b : ℕ → ℝ) (d : Fin n)
    (e : Equiv.Perm (Fin (r+1))) (D : PrefixPattern n (r+1) → ℝ) :
    prefixPatternMean n (r+1) b
      (fun Q => D (patternReindex Q e.symm)*(∑ j : Fin r, boolReal (Q 0 j.succ d))) =
      prefixPatternMean n (r+1) b
        (fun Q => D Q*(∑ j ∈ Finset.univ.erase (e 0), boolReal (Q (e 0) j d))) := by
  rw [← prefixPatternMean_perm n (r+1) b e]
  congr 1
  funext Q
  rw [patternReindex_perm_cancel]
  dsimp only [patternReindex]
  rw [sum_nonzero_permutation e (fun j => boolReal (Q (e 0) j d))]

lemma cascade_prefix_gg_all (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (i : Fin (r+1)) (d : Fin n) (D : PrefixPattern n (r+1) → ℝ) :
    (r+1 : ℕ)*prefixPatternMean n (r+1+1) b
      (fun Q => D (patternReindex Q Fin.castSucc)*boolReal (Q i.castSucc (Fin.last (r+1)) d)) =
      (1-b d)*prefixPatternMean n (r+1) b D +
      prefixPatternMean n (r+1) b
        (fun Q => D Q*(∑ j ∈ Finset.univ.erase i, boolReal (Q i j d))) := by
  have h := cascade_prefix_gg n r b hb d (fun Q => D (patternReindex Q (Equiv.swap 0 i).symm))
  rw [prefix_fresh_permuted,prefixPatternMean_perm,prefix_old_permuted,Equiv.swap_apply_left] at h
  exact h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def prefixVectorValue (n : ℕ) (a : ℕ → ℝ) (v : Fin n → Bool) : ℝ :=
  a 0+∑ d : Fin n, (a (d+1)-a d)*boolReal (v d)

lemma sum_prefix_telescope (n k : ℕ) (hk : k ≤ n) (a : ℕ → ℝ) :
    a 0+(∑ d : Fin n, (a (d+1)-a d)*(if d.val+1 ≤ k then 1 else 0)) = a k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    by_cases h : k ≤ n
    · have he : (∑ d : Fin n, (a (d.castSucc+1)-a d.castSucc)*(if d.castSucc.val+1 ≤ k then 1 else 0)) =
          ∑ d : Fin n, (a (d+1)-a d)*(if d.val+1 ≤ k then 1 else 0) := rfl
      rw [he]
      simp only [Fin.val_last,show ¬ n+1 ≤ k by omega,ite_false,mul_zero,add_zero]
      exact ih k h
    · have hkn : k = n+1 := by omega
      subst k
      have hs : (∑ d : Fin n, (a (d.castSucc+1)-a d.castSucc)*(if d.castSucc.val+1 ≤ n+1 then 1 else 0)) =
          ∑ d : Fin n, (a (d+1)-a d)*(if d.val+1 ≤ n then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd := d.isLt
        simp only [Fin.val_castSucc,show d.val+1 ≤ n+1 by omega,show d.val+1 ≤ n by omega,ite_true]
      rw [hs]
      simp only [Fin.val_last,le_refl,ite_true,mul_one]
      have hi := ih n (le_refl n)
      linarith

lemma prefixVectorValue_label (n : ℕ) (a : ℕ → ℝ) (v w : LabeledLeaf n) :
    prefixVectorValue n a (fun d => if (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) then true else false) =
      a (labeledCommonDepth n v w) := by
  unfold prefixVectorValue
  have hf : (fun d : Fin n => boolReal (if (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) then true else false)) =
      (fun d => if d.val+1 ≤ labeledCommonDepth n v w then 1 else 0) := by
    funext d
    simp only [labeled_prefix_eq_iff n v w (d := d.val+1) (by omega), boolReal]
    split <;> simp
  simp_rw [congrFun hf]
  exact sum_prefix_telescope n _ (labeledCommonDepth_le n v w) a

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPatternMean_restrict (n r : ℕ) (b : ℕ → ℝ) (D : PrefixPattern n r → ℝ) :
    prefixPatternMean n (r+1) b (fun Q => D (patternReindex Q Fin.castSucc)) = prefixPatternMean n r b D := rfl

def prefixGGResidual (n r : ℕ) (b : ℕ → ℝ) (i : Fin (r+1)) (D : PrefixPattern n (r+1) → ℝ) :
    ((Fin n → Bool) → ℝ) →ₗ[ℝ] ℝ where
  toFun V := (r+1 : ℕ)*prefixPatternMean n (r+1+1) b
      (fun Q => D (patternReindex Q Fin.castSucc)*V (Q i.castSucc (Fin.last (r+1)))) -
    prefixPatternMean n (r+1) b D*prefixPatternMean n 2 b (fun Q => V (Q 0 1)) -
    ∑ j ∈ Finset.univ.erase i, prefixPatternMean n (r+1) b (fun Q => D Q*V (Q i j))
  map_add' V W := by
    simp only [Pi.add_apply,mul_add,prefixPatternMean_add,Finset.sum_add_distrib]
    ring
  map_smul' c V := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,show ∀ x y : ℝ, x*(c*y) = c*(x*y) from fun x y => by ring,
      prefixPatternMean_mul,← Finset.mul_sum]
    ring

lemma prefixGGResidual_const (n r : ℕ) (b : ℕ → ℝ) (i : Fin (r+1)) (D : PrefixPattern n (r+1) → ℝ) :
    prefixGGResidual n r b i D (fun _ => 1) = 0 := by
  simp only [prefixGGResidual,LinearMap.coe_mk,AddHom.coe_mk,mul_one,
    prefixPatternMean_restrict,prefixPatternMean_const,Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,
    Nat.add_sub_cancel,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

lemma prefix_pair_mean_01 (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (d : Fin n) :
    prefixPatternMean n 2 b (fun Q => boolReal (Q 0 1 d)) = 1-b d := by
  rw [← prefix_pair_mean n b hb d]
  apply prefixPatternMean_congr
  intro σ
  simp [labelPrefixPattern,eq_comm]

lemma prefixGGResidual_level (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (i : Fin (r+1)) (d : Fin n) (D : PrefixPattern n (r+1) → ℝ) :
    prefixGGResidual n r b i D (fun v => boolReal (v d)) = 0 := by
  have h := cascade_prefix_gg_all n r b hb i d D
  have hs : prefixPatternMean n (r+1) b
      (fun Q => D Q*(∑ j ∈ Finset.univ.erase i, boolReal (Q i j d))) =
      ∑ j ∈ Finset.univ.erase i, prefixPatternMean n (r+1) b (fun Q => D Q*boolReal (Q i j d)) := by
    simp only [Finset.mul_sum,prefixPatternMean_sum]
  rw [hs] at h
  change (r+1 : ℕ)*prefixPatternMean n (r+1+1) b _ -
    prefixPatternMean n (r+1) b D*prefixPatternMean n 2 b (fun Q => boolReal (Q 0 1 d)) - _ = 0
  rw [prefix_pair_mean_01 n b hb d,h]
  ring

lemma prefixGGResidual_value (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (i : Fin (r+1)) (D : PrefixPattern n (r+1) → ℝ) (a : ℕ → ℝ) :
    prefixGGResidual n r b i D (prefixVectorValue n a) = 0 := by
  have he : prefixVectorValue n a = a 0 • (fun _ : Fin n → Bool => (1:ℝ))+
      ∑ d : Fin n, (a (d+1)-a d) • (fun v : Fin n → Bool => boolReal (v d)) := by
    funext v
    simp [prefixVectorValue,Finset.sum_apply]
  rw [he,map_add,map_smul,map_sum,prefixGGResidual_const]
  simp only [map_smul,prefixGGResidual_level n r b hb i,smul_zero,Finset.sum_const_zero,add_zero]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

def cascadeScalarArray (n : ℕ) (a : ℕ → ℝ) (σ : ℕ → LabeledLeaf n) : RealArray :=
  fun i j => a (labeledCommonDepth n (σ i) (σ j))

lemma measurable_cascadeScalarArray (n : ℕ) (a : ℕ → ℝ) : Measurable (cascadeScalarArray n a) := by
  unfold cascadeScalarArray
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  have h : Measurable (fun p : LabeledLeaf n × LabeledLeaf n => a (labeledCommonDepth n p.1 p.2)) := measurable_of_countable _
  exact h.comp (show Measurable (fun σ : ℕ → LabeledLeaf n => (σ i,σ j)) by fun_prop)

lemma prefixVectorValue_pattern (n r : ℕ) (a : ℕ → ℝ) (σ : Fin r → LabeledLeaf n) (i j : Fin r) :
    prefixVectorValue n a (labelPrefixPattern n r σ i j) = a (labeledCommonDepth n (σ i) (σ j)) :=
  prefixVectorValue_label n a (σ i) (σ j)

lemma integral_ite_one_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω)
    (hA : MeasurableSet A) : (∫ ω, (if ω ∈ A then (1:ℝ) else 0) ∂μ) = μ.real A := by
  classical
  simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ := μ) hA

lemma integral_ite_one_mul_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ ω, (if ω ∈ A then (1:ℝ) else 0)*(if ω ∈ B then 1 else 0) ∂μ) = μ.real (A ∩ B) := by
  classical
  rw [← integral_ite_one_eq μ (A ∩ B) (hA.inter hB)]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha,hb]

 

theorem cascade_scalar_gg (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ) :
    HasGhirlandaGuerra (cascadeScalarArray n a) (cascadeReplicaLaw n b) := by
  classical
  intro m hm i A hA t ht
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let D : PrefixPattern n (r+1) → ℝ := fun Q =>
    if (fun i j => prefixVectorValue n a (Q i j)) ∈ A then 1 else 0
  let c : ℕ → ℝ := fun k => if a k ∈ t then 1 else 0
  have h := prefixGGResidual_value n r b hb i D c
  change (r+1 : ℕ)*prefixPatternMean n (r+1+1) b
      (fun Q => D (patternReindex Q Fin.castSucc)*prefixVectorValue n c (Q i.castSucc (Fin.last (r+1)))) -
    prefixPatternMean n (r+1) b D*prefixPatternMean n 2 b (fun Q => prefixVectorValue n c (Q 0 1)) -
    (∑ j ∈ Finset.univ.erase i, prefixPatternMean n (r+1) b (fun Q => D Q*prefixVectorValue n c (Q i j))) = 0 at h
  simp only [prefixPatternMean,D] at h
  simp only [patternReindex_label,prefixVectorValue_pattern,Function.comp_apply,Fin.val_castSucc,Fin.val_last,c] at h
  have hAm : MeasurableSet (arrayBlock (cascadeScalarArray n a) (r+1) ⁻¹' A) :=
    hA.preimage (measurable_arrayBlock (measurable_cascadeScalarArray n a) _)
  have htm : ∀ i j, MeasurableSet {σ | cascadeScalarArray n a σ i j ∈ t} :=
    fun i j => ht.preimage ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_cascadeScalarArray n a)))
  change (r+1 : ℕ)*(∫ σ, (if arrayBlock (cascadeScalarArray n a) (r+1) σ ∈ A then (1:ℝ) else 0)*
      (if cascadeScalarArray n a σ i (r+1) ∈ t then 1 else 0) ∂cascadeReplicaLaw n b) -
    (∫ σ, (if arrayBlock (cascadeScalarArray n a) (r+1) σ ∈ A then (1:ℝ) else 0) ∂cascadeReplicaLaw n b)*
      (∫ σ, (if cascadeScalarArray n a σ 0 1 ∈ t then (1:ℝ) else 0) ∂cascadeReplicaLaw n b) -
    (∑ j ∈ Finset.univ.erase i, ∫ σ, (if arrayBlock (cascadeScalarArray n a) (r+1) σ ∈ A then (1:ℝ) else 0)*
      (if cascadeScalarArray n a σ i j ∈ t then 1 else 0) ∂cascadeReplicaLaw n b) = 0 at h
  have hint (u v : ℕ) : (∫ σ, (if arrayBlock (cascadeScalarArray n a) (r+1) σ ∈ A then (1:ℝ) else 0)*
      (if cascadeScalarArray n a σ u v ∈ t then 1 else 0) ∂cascadeReplicaLaw n b) =
      (cascadeReplicaLaw n b).real ((arrayBlock (cascadeScalarArray n a) (r+1) ⁻¹' A) ∩ {σ | cascadeScalarArray n a σ u v ∈ t}) :=
    integral_ite_one_mul_eq _ _ _ hAm (htm u v)
  have htest : (∫ σ, (if arrayBlock (cascadeScalarArray n a) (r+1) σ ∈ A then (1:ℝ) else 0) ∂cascadeReplicaLaw n b) =
      (cascadeReplicaLaw n b).real (arrayBlock (cascadeScalarArray n a) (r+1) ⁻¹' A) := integral_ite_one_eq _ _ hAm
  have hpair : (∫ σ, (if cascadeScalarArray n a σ 0 1 ∈ t then (1:ℝ) else 0) ∂cascadeReplicaLaw n b) =
      (cascadeReplicaLaw n b).real {σ | cascadeScalarArray n a σ 0 1 ∈ t} := integral_ite_one_eq _ _ (htm 0 1)
  simp only [hint,htest,hpair] at h
  have hr : ((r+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← add_div]
  apply (eq_div_iff hr).2
  nlinarith [h]

end IsingPerceptron

end

end OAI
