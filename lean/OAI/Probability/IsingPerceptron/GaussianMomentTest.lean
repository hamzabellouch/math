import Mathlib
import OAI.Probability.IsingPerceptron.CascadePair

namespace OAI

/-! Gaussian Moment Test. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction
namespace IsingPerceptron

def gaussianMoment (m : ℕ) (f : ℝ → ℝ) (S : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∫ z : EuclideanSpace ℝ (Fin m), Real.exp (∑ i, f (z i)) ∂multivariateGaussian 0 S

lemma gaussianMoment_bound (m : ℕ) {f : ℝ → ℝ} {K : ℝ} (hf : ∀ x, |f x| ≤ K)
    (S : Matrix (Fin m) (Fin m) ℝ) : |gaussianMoment m f S| ≤ Real.exp (m*K) := by
  have h (z : EuclideanSpace ℝ (Fin m)) : ‖Real.exp (∑ i, f (z i))‖ ≤ Real.exp (m*K) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ : Fin m, K := Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hf (z i)))
      _ = _ := by simp
  simpa only [gaussianMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S)
      (ae_of_all _ h)

lemma gaussianMoment_extension (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    ∃ F : Matrix (Fin m) (Fin m) ℝ →ᵇ ℝ,
      ∀ S, S.PosSemidef → F S = gaussianMoment m f S := by
  let : NormalSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (NormalSpace (Fin m → Fin m → ℝ))
  let g : PositiveCovariance m →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun S => gaussianMoment m f S.val) (continuous_gaussianMoment m hf hK) (Real.exp (m*K))
    (fun S => by simpa only [Real.norm_eq_abs] using gaussianMoment_bound m hK S.val)
  obtain ⟨F,_,hF⟩ := g.exists_norm_eq_domRestrict_eq_of_closed (isClosed_setOf_posSemidef m)
  exact ⟨F,fun S hS => congrArg (fun g : PositiveCovariance m →ᵇ ℝ => g ⟨S,hS⟩) hF⟩

 

theorem jointArray_tendsto_gaussianMoment {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure JointArray), GramDiagonal 1 (spinArray x))
    (hGμ : ∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x))
    (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Tendsto (fun k => ∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(L k : Measure JointArray)) atTop
      (𝓝 (∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray))) := by
  obtain ⟨F,hF⟩ := gaussianMoment_extension m hf hK
  have he (P : ProbabilityMeasure JointArray) (hP : ∀ᵐ x ∂(P : Measure JointArray), GramDiagonal 1 (spinArray x)) :
      (∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(P : Measure JointArray)) =
      ∫ x, F (fun i j : Fin m => spinArray x i j) ∂(P : Measure JointArray) := by
    apply integral_congr_ae
    filter_upwards [hP] with x hx
    exact (hF _ (hx.1 m)).symm
  simp_rw [he _ (hGμ),he _ (hG _)]
  exact jointArray_tendsto_integral hL (F.continuous.comp (by unfold spinArray; fun_prop))

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

def freshPatternFactor {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (A : X → ℕ →₀ ℝ) (f : ℝ → ℝ) (g : ℕ → ℝ) : ℝ :=
  ∫ x, Real.exp (f (cylinderField (A x) g)) ∂ν

lemma freshPatternFactor_bound {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) (f : ℝ → ℝ) {K : ℝ} (hK : ∀ x, |f x| ≤ K) (g : ℕ → ℝ) :
    freshPatternFactor ν A f g ∈ Icc (Real.exp (-K)) (Real.exp K) := by
  have hi : Integrable (fun x => Real.exp (f (cylinderField (A x) g))) ν :=
    Integrable.of_bound (.of_discrete) (Real.exp K) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK _))))
  constructor
  · calc
      Real.exp (-K) = ∫ _ : X, Real.exp (-K) ∂ν := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi (fun x =>
        Real.exp_le_exp.mpr (abs_le.mp (hK _)).1)
  · calc
      _ ≤ ∫ _ : X, Real.exp K ∂ν := integral_mono hi (integrable_const _) (fun x =>
        Real.exp_le_exp.mpr (abs_le.mp (hK _)).2)
      _ = _ := by simp

lemma gaussianMoment_cylinder_integral {m : ℕ} (A : Fin m → ℕ →₀ ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) :
    gaussianMoment m f (fun i j => cylinderCross (A i) (A j)) =
      ∫ g, Real.exp (∑ i, f (cylinderField (A i) g)) ∂gaussianCoordinates := by
  unfold gaussianMoment
  rw [← cylinder_vector_law A]
  have hint : Measurable (fun z : EuclideanSpace ℝ (Fin m) => Real.exp (∑ i, f (z i))) := by
    exact (Finset.measurable_sum _ (fun i _ => hf.comp (by fun_prop))).exp
  have hmap : Measurable (fun g =>
      (WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m))) :=
    (by fun_prop : Measurable (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))).comp
      (Measurable.of_eval (fun i => measurable_cylinderField (A i)))
  rw [integral_map hmap.aemeasurable hint.aestronglyMeasurable]

lemma freshGaussianReplica_integrable {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    Integrable (fun x : (Fin m → X) × (ℕ → ℝ) =>
      Real.exp (∑ i, f (cylinderField (A (x.1 i)) x.2)))
      ((Measure.pi (fun _ : Fin m => ν)).prod gaussianCoordinates) := by
  have hm : Measurable (fun x : (Fin m → X) × (ℕ → ℝ) =>
      Real.exp (∑ i, f (cylinderField (A (x.1 i)) x.2))) := by
    apply Measurable.exp
    apply Finset.measurable_sum
    intro i _
    exact hf.comp ((measurable_cylinderFields A).comp
      (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)))
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (m*K))
  exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ∑ _ : Fin m, K := Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hK _))
        _ = _ := by simp)

lemma freshPatternFactor_pow {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (A : X → ℕ →₀ ℝ) (f : ℝ → ℝ) (m : ℕ) (g : ℕ → ℝ) : (freshPatternFactor ν A f g)^m =
      ∫ σ : Fin m → X, Real.exp (∑ i, f (cylinderField (A (σ i)) g)) ∂Measure.pi (fun _ => ν) := by
    simp only [Real.exp_sum]
    simpa only [Fintype.card_fin,freshPatternFactor] using
      (integral_fintype_prod_eq_pow (ι := Fin m) (μ := ν)
        (fun x => Real.exp (f (cylinderField (A x) g)))).symm

lemma freshPatternFactor_moment {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ g, (freshPatternFactor ν A f g)^m ∂gaussianCoordinates) =
      ∫ σ : Fin m → X, gaussianMoment m f
        (fun i j => cylinderCross (A (σ i)) (A (σ j))) ∂Measure.pi (fun _ => ν) := by
  have he := freshPatternFactor_pow ν A f m
  calc
    _ = ∫ g, ∫ σ : Fin m → X, Real.exp (∑ i, f (cylinderField (A (σ i)) g))
        ∂Measure.pi (fun _ => ν) ∂gaussianCoordinates := integral_congr_ae (ae_of_all _ he)
    _ = ∫ σ : Fin m → X, ∫ g, Real.exp (∑ i, f (cylinderField (A (σ i)) g))
        ∂gaussianCoordinates ∂Measure.pi (fun _ => ν) := by
      have hi := freshGaussianReplica_integrable ν A hf hK m
      exact (integral_integral_swap hi).symm
    _ = _ := integral_congr_ae (ae_of_all _ (fun σ =>
      (gaussianMoment_cylinder_integral (fun i => A (σ i)) hf).symm))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma measurable_random_freshPatternFactor {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun z : Ω × (ℕ → ℝ) => freshPatternFactor (ν z.1) A f z.2) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst) (hf.comp ((measurable_cylinderFields A).comp
      (measurable_fst.snd.prodMk measurable_snd)))

 

theorem freshPatternFactor_array_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) (κ : X → X → JointEntry)
    (hA : ∀ x y, cylinderCross (A x) (A y) = (κ x y).1.1)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ z : Ω × (ℕ → ℝ), (freshPatternFactor (ν z.1) A f z.2)^m ∂P.prod gaussianCoordinates) =
      ∫ x, gaussianMoment m f (fun i j => spinArray x i j)
        ∂(overlapArrayLaw P ν hν κ : Measure JointArray) := by
  obtain ⟨F,hF⟩ := gaussianMoment_extension m hf hK
  let E : JointArray → ℝ := fun x => F (fun i j : Fin m => spinArray x i j)
  have hE : Continuous E := F.continuous.comp (by unfold spinArray; fun_prop)
  have hG : ∀ᵐ x ∂(overlapArrayLaw P ν hν κ : Measure JointArray),
      Matrix.PosSemidef (fun i j : Fin m => spinArray x i j) := by
    change ∀ᵐ x ∂(replicaLaw P ν hν).map (sampledOverlapArray κ), _
    apply (ae_map_iff (measurable_sampledOverlapArray κ).aemeasurable
      ((isClosed_setOf_posSemidef m).preimage (by unfold spinArray; fun_prop)).measurableSet).mpr
    apply ae_of_all
    intro σ
    change Matrix.PosSemidef (fun i j : Fin m => spinArray (sampledOverlapArray κ σ) i j)
    have heq : (fun i j : Fin m => spinArray (sampledOverlapArray κ σ) i j) =
        (fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j))) := by
      funext i j
      exact (hA _ _).symm
    rw [heq]
    exact cylinderCross_matrix_posSemidef (fun i : Fin m => A (σ i))
  have hmean : (∫ x, gaussianMoment m f (fun i j => spinArray x i j)
      ∂(overlapArrayLaw P ν hν κ : Measure JointArray)) =
      ∫ x, E x ∂(overlapArrayLaw P ν hν κ : Measure JointArray) := by
    apply integral_congr_ae
    filter_upwards [hG] with x hx
    exact (hF _ hx).symm
  rw [hmean]
  change _ = ∫ x, E x ∂(replicaLaw P ν hν).map (sampledOverlapArray κ)
  rw [integral_map (measurable_sampledOverlapArray κ).aemeasurable hE.measurable.aestronglyMeasurable]
  have he (σ : ℕ → X) : E (sampledOverlapArray κ σ) =
      gaussianMoment m f (fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j))) := by
    have heq : (fun i j : Fin m => spinArray (sampledOverlapArray κ σ) i j) =
        fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j)) := by
      funext i j; exact (hA _ _).symm
    change F _ = _
    rw [heq]
    exact hF _ (cylinderCross_matrix_posSemidef _)
  simp_rw [he]
  rw [replicaLaw_integral_prefix P ν hν
    (fun σ : Fin m → X => gaussianMoment m f (fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j))))
    (fun σ => gaussianMoment_bound m hK _)]
  have hi : Integrable (fun z : Ω × (ℕ → ℝ) => (freshPatternFactor (ν z.1) A f z.2)^m)
      (P.prod gaussianCoordinates) := by
    apply Integrable.of_bound ((measurable_random_freshPatternFactor hν A hf.measurable).pow_const m).aestronglyMeasurable
      ((Real.exp K)^m)
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg ((Real.exp_pos _).le.trans (freshPatternFactor_bound (ν z.1) A f hK z.2).1)]
      exact pow_le_pow_left₀ ((Real.exp_pos _).le.trans (freshPatternFactor_bound (ν z.1) A f hK z.2).1)
        (freshPatternFactor_bound (ν z.1) A f hK z.2).2 _)
  rw [integral_prod _ hi]
  exact integral_congr_ae (ae_of_all _ (fun ω => freshPatternFactor_moment (ν ω) A hf.measurable hK m))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def labeledScalarFactor (n : ℕ) (s : ℕ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (p : LabeledTree n × (ForestVertex n → ℝ)) : ℝ :=
  ∫ v, Real.exp (F (x+∑ i : Fin n, s i*p.2 (edgeAt n v i))) ∂labeledLeafLaw n p.1

lemma measurable_labeledScalarFactor (n : ℕ) (s : ℕ → ℝ) {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun p : ℝ × (LabeledTree n × (ForestVertex n → ℝ)) => labeledScalarFactor n s F p.1 p.2) := by
  change Measurable (fun p : ℝ × (LabeledTree n × (ForestVertex n → ℝ)) =>
    referencePartition (labeledLeafLaw n p.2.1) (fun v => F (p.1+∑ i : Fin n, s i*p.2.2 (edgeAt n v i))))
  apply measurable_random_referencePartition (ν := fun p : ℝ × (LabeledTree n × (ForestVertex n → ℝ)) => labeledLeafLaw n p.2.1)
    ((measurable_labeledLeafLaw n).comp (by fun_prop))
    (H := fun p : (ℝ × (LabeledTree n × (ForestVertex n → ℝ))) × LabeledLeaf n => F (p.1.1+∑ i : Fin n, s i*p.1.2.2 (edgeAt n p.2 i)))
  apply hF.comp
  apply Measurable.add (by fun_prop)
  apply Finset.measurable_sum
  intro i _
  apply Measurable.const_mul
  have hv : Measurable (fun p : (ForestVertex n → ℝ) × LabeledLeaf n => p.1 (edgeAt n p.2 i)) :=
    measurable_from_prod_countable_left (fun v => measurable_pi_apply (edgeAt n v i))
  exact hv.comp (by fun_prop : Measurable (fun p : (ℝ × (LabeledTree n × (ForestVertex n → ℝ))) × LabeledLeaf n => (p.1.2.2,p.2)))

lemma labeledScalar_log_bound (n : ℕ) (s : ℕ → ℝ) (F : ℝ → ℝ) {K : ℝ}
    (hF : ∀ y, |F y| ≤ K) (x : ℝ) (p : LabeledTree n × (ForestVertex n → ℝ)) :
    |Real.log (labeledScalarFactor n s F x p)| ≤ K := by
  simpa only [logMean,one_mul,div_one,labeledScalarFactor] using
    logMean_bounds (labeledLeafLaw n p.1) (measurable_of_countable (fun v => F (x+∑ i : Fin n, s i*p.2 (edgeAt n v i))))
      (b := 1) zero_lt_one (fun v => hF _)

lemma labeledScalarFactor_eq_noise (n : ℕ) (b s : ℕ → ℝ) (hb : CascadeExponents n b)
    {F : ℝ → ℝ} (hF : Measurable F) (x : ℝ) :
    ∀ᵐ p ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)),
      labeledScalarFactor n s F x p =
        ∫ v, Real.exp (noiseLeafTerminal n (fun _ => F) (fun i p => p.1+s i*p.2) x v)
          ∂noiseLeafKernel ℝ n (labeledNoiseJoin ℝ n (p.1,markForestOfCoords ℝ n p.2)) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun _ => ⟨gaussianReal 0 1,inferInstance⟩
  let T := fun p : LabeledTree n × (ForestVertex n → ℝ) =>
    labeledNoiseJoin ℝ n (p.1,markForestOfCoords ℝ n p.2)
  have hp : MeasurePreserving T ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)))
      (noiseCascadeLaw ℝ n b μ : Measure (NoiseTree ℝ n)) :=
    ⟨by fun_prop,labeledNoiseCoordinates_law ℝ n b μ⟩
  filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good ℝ n b hb μ)] with p hg
  have htot : 0 < noiseTreeTotal ℝ n (T p) ∧ noiseTreeTotal ℝ n (T p) < ∞ := by
    cases n with
    | zero => simp [noiseTreeTotal,rawTreeTotal]
    | succ n => exact hg.1
  have hmap := labeledLeafLaw_noiseMap ℝ n p.1 (markForestOfCoords ℝ n p.2) hg htot
  have hm : Measurable (fun v : NoiseLeaf ℝ n => Real.exp (noiseLeafTerminal n (fun _ => F) (fun i p => p.1+s i*p.2) x v)) :=
    ((measurable_noiseLeafTerminal n (fun _ => hF) (fun i => by fun_prop)).comp
      (measurable_const.prodMk measurable_id)).exp
  rw [← hmap,integral_map (measurable_of_countable _).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [noiseLeafTerminal_additive,noiseLeafMark_labeled]

 

theorem labeledScalar_log_recursion (n : ℕ) (b s : ℕ → ℝ) (hb : CascadeExponents n b)
    {F : ℝ → ℝ} (hF : Measurable F) {K : ℝ} (hbound : ∀ y, |F y| ≤ K) (x : ℝ) :
    (∫ p, Real.log (labeledScalarFactor n s F x p)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1))) =
      cascadeRecursion n b (fun _ => ⟨gaussianReal 0 1,inferInstance⟩)
        (fun i p => p.1+s i*p.2) F x := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun _ => ⟨gaussianReal 0 1,inferInstance⟩
  let T := fun p : LabeledTree n × (ForestVertex n → ℝ) =>
    labeledNoiseJoin ℝ n (p.1,markForestOfCoords ℝ n p.2)
  have hp : MeasurePreserving T ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)))
      (noiseCascadeLaw ℝ n b μ : Measure (NoiseTree ℝ n)) :=
    ⟨by fun_prop,labeledNoiseCoordinates_law ℝ n b μ⟩
  have hr := bounded_cascade_leaf_recursion n b hb μ
    (fun i => (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1+s i*p.2))) hF hbound x
  calc
    _ = ∫ p, Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => F) (fun i p => p.1+s i*p.2) x v)
        ∂noiseLeafKernel ℝ n (T p)) ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)) := by
      apply integral_congr_ae
      filter_upwards [labeledScalarFactor_eq_noise n b s hb hF x] with p hp
      rw [hp]
    _ = _ := by
      have he := (HasLaw.mk hp.measurable.aemeasurable hp.map_eq).integral_comp hr.1.aestronglyMeasurable
      exact he.trans hr.2

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

def rowFactor (c : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, Real.exp (f (y+Real.sqrt c*z)) ∂gaussianReal 0 1

lemma measurable_rowFactor (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) : Measurable (rowFactor c f) := by
  exact (hf.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1+Real.sqrt c*p.2))).exp.stronglyMeasurable.integral_prod_right'.measurable

lemma rowFactor_bound (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (y : ℝ) :
    rowFactor c f y ∈ Icc (Real.exp (-K)) (Real.exp K) := by
  have hi : Integrable (fun z => Real.exp (f (y+Real.sqrt c*z))) (gaussianReal 0 1) := by
    apply Integrable.of_bound (hf.comp (by fun_prop)).exp.aestronglyMeasurable (Real.exp K)
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (abs_le.mp (hb _)).2
  constructor
  · calc
      Real.exp (-K) = ∫ _ : ℝ, Real.exp (-K) ∂gaussianReal 0 1 := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi (fun z => Real.exp_le_exp.mpr (abs_le.mp (hb _)).1)
  · calc
      _ ≤ ∫ _ : ℝ, Real.exp K ∂gaussianReal 0 1 :=
        integral_mono hi (integrable_const _) (fun z => Real.exp_le_exp.mpr (abs_le.mp (hb _)).2)
      _ = _ := by simp

lemma gaussianTransform_one (c : ℝ) (f : ℝ → ℝ) : gaussianTransform c 1 f = fun y => Real.log (rowFactor c f y) := by
  funext y
  simp [gaussianTransform,rowFactor]

lemma exp_gaussianTransform_one (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (y : ℝ) :
    Real.exp (gaussianTransform c 1 f y) = rowFactor c f y := by
  rw [gaussianTransform_one,Real.exp_log ((Real.exp_pos (-K)).trans_le (rowFactor_bound c hf hb y).1)]

lemma gaussianTransform_one_bound (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (y : ℝ) : |gaussianTransform c 1 f y| ≤ K := by
  have h := rowFactor_bound c hf hb y
  rw [gaussianTransform_one]
  apply abs_le.mpr
  constructor
  · have hh := Real.log_le_log (Real.exp_pos (-K)) h.1
    simpa only [Real.log_exp] using hh
  · have hh := Real.log_le_log ((Real.exp_pos (-K)).trans_le h.1) h.2
    simpa only [Real.log_exp] using hh

lemma rowFactor_product {m : ℕ} (c : ℝ) (f : ℝ → ℝ) (y : Fin m → ℝ) :
    (∏ i, rowFactor c f (y i)) =
      ∫ z : Fin m → ℝ, Real.exp (∑ i, f (y i+Real.sqrt c*z i))
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  simp only [Real.exp_sum]
  exact (integral_fintype_prod_eq_prod (fun i z => Real.exp (f (y i+Real.sqrt c*z)))).symm

lemma gaussianCoordinates_prefix {m : ℕ} :
    MeasurePreserving (fun g : ℕ → ℝ => fun i : Fin m => g i) gaussianCoordinates
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
  refine ⟨by fun_prop,?_⟩
  exact replica_prefix_map (gaussianReal 0 1) m

lemma rowFactor_product_coordinates {m : ℕ} (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (y : Fin m → ℝ) :
    (∏ i, rowFactor c f (y i)) =
      ∫ z : ℕ → ℝ, Real.exp (∑ i, f (y i+Real.sqrt c*z i)) ∂gaussianCoordinates := by
  rw [rowFactor_product]
  exact (HasLaw.integral_comp ⟨gaussianCoordinates_prefix.measurable.aemeasurable,gaussianCoordinates_prefix.map_eq⟩
    (f := fun z : Fin m → ℝ => Real.exp (∑ i, f (y i+Real.sqrt c*z i))) ((Finset.measurable_sum _ (fun i _ => hf.comp (by fun_prop))).exp.aestronglyMeasurable)).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma residualGaussian_integrable {m : ℕ} (A : Fin m → ℕ →₀ ℝ) (c : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hb : ∀ y, |f y| ≤ K) :
    Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      Real.exp (∑ i, f (cylinderField (A i) p.1+Real.sqrt c*p.2 i)))
      (gaussianCoordinates.prod gaussianCoordinates) := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      Real.exp (∑ i, f (cylinderField (A i) p.1+Real.sqrt c*p.2 i))) := by
    apply Measurable.exp
    apply Finset.measurable_sum
    intro i _
    exact hf.comp (((measurable_cylinderField (A i)).comp measurable_fst).add (by fun_prop))
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (m*K))
  filter_upwards [] with p
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ _ : Fin m, K := Finset.sum_le_sum (fun i _ => (abs_le.mp (hb _)).2)
    _ = _ := by simp

 

lemma gaussianMoment_residual {m : ℕ} (A : Fin m → ℕ →₀ ℝ) {c : ℝ} (hc : 0 ≤ c)
    {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hb : ∀ y, |f y| ≤ K) :
    gaussianMoment m (gaussianTransform c 1 f) (fun i j => cylinderCross (A i) (A j)) =
      gaussianMoment m f (fun i j => cylinderCross (A i) (A j)+(if i=j then c else 0)) := by
  classical
  let B : Fin m → ℕ →₀ ℝ := fun i => Finsupp.single i.val 1
  let C := gaussianSumCoefficients A B (Real.sqrt c)
  have hC (i j : Fin m) : cylinderCross (C i) (C j) =
      cylinderCross (A i) (A j)+(if i=j then c else 0) := by
    rw [gaussianSumCoefficients_cross,Real.sq_sqrt hc]
    simp only [B,cylinderCross_single_left,one_mul,Finsupp.single_apply,Fin.val_inj]
    by_cases h : i=j
    · simp [h]
    · simp [h,Ne.symm h]
  have hfield (i : Fin m) (g : ℕ → ℝ) : cylinderField (C i) g =
      cylinderField (A i) (gaussianPair g).1+Real.sqrt c*(gaussianPair g).2 i := by
    rw [gaussianSumCoefficients_field]
    simp [B,cylinderField]
  rw [gaussianMoment_cylinder_integral A (by rw [gaussianTransform_one]; exact (measurable_rowFactor c hf).log)]
  have hR : (fun i j => cylinderCross (A i) (A j)+(if i=j then c else 0)) =
      (fun i j => cylinderCross (C i) (C j)) := funext (fun i => funext (fun j => (hC i j).symm))
  rw [hR,gaussianMoment_cylinder_integral C hf]
  calc
    _ = ∫ g, ∫ z : ℕ → ℝ, Real.exp (∑ i, f (cylinderField (A i) g+Real.sqrt c*z i)) ∂gaussianCoordinates ∂gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [Real.exp_sum]
      simp_rw [exp_gaussianTransform_one c hf hb]
      exact rowFactor_product_coordinates c hf (fun i => cylinderField (A i) g)
    _ = ∫ p : (ℕ → ℝ) × (ℕ → ℝ), Real.exp (∑ i, f (cylinderField (A i) p.1+Real.sqrt c*p.2 i))
        ∂gaussianCoordinates.prod gaussianCoordinates := (integral_prod _ (residualGaussian_integrable A c hf hb)).symm
    _ = _ := by
      have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
          Real.exp (∑ i, f (cylinderField (A i) p.1+Real.sqrt c*p.2 i))) := by
        apply Measurable.exp
        apply Finset.measurable_sum
        intro i _
        exact hf.comp (((measurable_cylinderField (A i)).comp measurable_fst).add (by fun_prop))
      have he := (HasLaw.mk gaussianPair_preserving.measurable.aemeasurable gaussianPair_preserving.map_eq).integral_comp hm.aestronglyMeasurable
      rw [← he]
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [Function.comp_apply,hfield]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma labeledCommonDepth_ultrametric (n : ℕ) (v w z : LabeledLeaf n) :
    min (labeledCommonDepth n v z) (labeledCommonDepth n w z) ≤ labeledCommonDepth n v w := by
  let d := min (labeledCommonDepth n v z) (labeledCommonDepth n w z)
  have hd : d ≤ n := (min_le_left _ _).trans (labeledCommonDepth_le n v z)
  apply (labeled_prefix_eq_iff n v w hd).mp
  exact ((labeled_prefix_eq_iff n v z hd).mpr (min_le_left _ _)).trans
    ((labeled_prefix_eq_iff n w z hd).mpr (min_le_right _ _)).symm

lemma monotone_labeledCommonDepth_ultrametric (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a)
    (v w z : LabeledLeaf n) :
    min (a (labeledCommonDepth n v z)) (a (labeledCommonDepth n w z)) ≤ a (labeledCommonDepth n v w) := by
  have h := ha (labeledCommonDepth_ultrametric n v w z)
  rcases le_total (labeledCommonDepth n v z) (labeledCommonDepth n w z) with he|he
  · simpa only [min_eq_left he,min_eq_left (ha he)] using h
  · simpa only [min_eq_right he,min_eq_right (ha he)] using h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Classical
namespace IsingPerceptron

def diagonalPatch {I : Type*} [DecidableEq I] (D : ℝ) (B : I → I → ℝ) : I → I → ℝ :=
  fun i j => if i=j then D else B i j

lemma measurable_diagonalPatch {I : Type*} [DecidableEq I] (D : ℝ) : Measurable (diagonalPatch (I := I) D) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  unfold diagonalPatch
  split_ifs <;> fun_prop

lemma diagonalPatch_arrayBlock (D : ℝ) {Ω : Type*} (B : Ω → RealArray) (n : ℕ) (ω : Ω) :
    arrayBlock (fun ω => diagonalPatch D (B ω)) n ω = diagonalPatch D (arrayBlock B n ω) := by
  funext i j
  simp only [arrayBlock,diagonalPatch,Fin.val_inj]

lemma HasGhirlandaGuerra.patchDiagonal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (h : HasGhirlandaGuerra B μ) (D : ℝ) :
    HasGhirlandaGuerra (fun ω => diagonalPatch D (B ω)) μ := by
  intro n hn i A hA t ht
  have h0 := h n hn i (diagonalPatch D ⁻¹' A) (hA.preimage (measurable_diagonalPatch D)) t ht
  have hin : (i.val : ℕ) ≠ n := Nat.ne_of_lt i.isLt
  have he : ∀ j ∈ Finset.univ.erase i, j ≠ i := fun j hj => (Finset.mem_erase.mp hj).1
  have hs : (arrayBlock (fun ω => diagonalPatch D (B ω)) n ⁻¹' A) = (arrayBlock B n ⁻¹' (diagonalPatch D ⁻¹' A)) := by
    ext ω
    simp only [Set.mem_preimage,diagonalPatch_arrayBlock]
  rw [hs]
  simp only [diagonalPatch,ite_false,hin,show (0:ℕ) ≠ 1 by omega]
  rw [h0]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i.val ≠ j.val := fun hval => he j hj (Fin.ext hval).symm
  simp only [hij,ite_false]

lemma diagonalPatch_ultrametric {B : RealArray} (D : ℝ) (hs : ∀ i j, B i j = B j i)
    (hB : IsUltrametricArray B) (hb : ∀ i j, B i j ≤ D) :
    IsUltrametricArray (diagonalPatch D B) := by
  intro i j k
  by_cases hij : i=j
  · subst j
    by_cases hik : i=k
    · subst k; simp [diagonalPatch]
    · simp [diagonalPatch,hik,hb]
  · by_cases hik : i=k
    · subst k
      simpa only [diagonalPatch,ite_true,hij,ite_false,Ne.symm hij,hs j i] using (min_le_right D (B i j))
    · by_cases hjk : j=k
      · subst k
        simpa only [diagonalPatch,ite_true,hij,ite_false] using (min_le_left (B i j) D)
      · simpa only [diagonalPatch,hij,hik,hjk,ite_false] using hB i j k

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

 

theorem cascade_blockLaw_unique {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hGG : HasGhirlandaGuerra B μ)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω)) {D : ℝ}
    (hd : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ)
    (ha : Monotone a) (haD : a n ≤ D)
    (hp : μ.map (fun ω => B ω 0 1) =
      (cascadeReplicaLaw n b).map (fun σ => cascadeScalarArray n a σ 0 1)) :
    ∀ r, blockLaw B μ r = blockLaw (fun σ => diagonalPatch D (cascadeScalarArray n a σ))
      (cascadeReplicaLaw n b) r := by
  apply gg_blockLaw_unique hm ((measurable_diagonalPatch D).comp (measurable_cascadeScalarArray n a))
    hGG ((cascade_scalar_gg n b hb a).patchDiagonal D) hs
  · filter_upwards [] with σ i j
    simp only [Function.comp_apply]
    unfold diagonalPatch cascadeScalarArray
    by_cases h : i=j
    · subst j; rfl
    · simp only [h,Ne.symm h,ite_false,labeledCommonDepth_symm n (σ i) (σ j)]
  · exact hu
  · filter_upwards [] with σ
    apply diagonalPatch_ultrametric D
    · exact fun i j => congrArg a (labeledCommonDepth_symm n (σ i) (σ j))
    · exact fun i j k => monotone_labeledCommonDepth_ultrametric n ha (σ i) (σ j) (σ k)
    · exact fun i j => (ha (labeledCommonDepth_le n (σ i) (σ j))).trans haD
  · exact hd
  · filter_upwards [] with σ i
    simp only [Function.comp_apply,diagonalPatch,ite_true]
  · simpa only [Function.comp_apply,diagonalPatch,show (0:ℕ) ≠ 1 by omega,ite_false] using hp

end IsingPerceptron

end

end OAI
