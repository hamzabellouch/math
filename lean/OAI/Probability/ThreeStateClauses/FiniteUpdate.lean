import Mathlib
import OAI.Probability.ThreeStateClauses.Basic
import OAI.Probability.ThreeStateClauses.DiscreteLaw
import OAI.Probability.ThreeStateClauses.Products
import OAI.Probability.ThreeStateClauses.BranchMoments

namespace OAI

/-! Finite Update. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

def branchOutput {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) {n : ℕ}
    (m : Fin n → Message) : Message :=
  ⟨normalizedProduct (branchEdges lam m),
    (fun i ↦ (normalizedProduct_positive (branchEdges_positive hl₀ hl₁ m)).1 i |>.le),
    (normalizedProduct_positive (branchEdges_positive hl₀ hl₁ m)).2⟩

lemma continuous_branchOutput {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    Continuous (branchOutput hl₀ hl₁ (n := n)) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i ↦ (continuous_branchProduct lam i).div (continuous_normalizer n lam)
    (fun m ↦ ne_of_gt (normalizer_positive (branchEdges_positive hl₀ hl₁ m))))

def tiltedProduct (Q : Law) (lam : ℝ) (n : ℕ) : Measure (Fin n → Message) :=
  (Measure.pi fun _ ↦ Q.probability.toMeasure).withDensity
    (fun m ↦ ENNReal.ofReal (normalizer (branchEdges lam m)))

lemma tiltedProduct_isProbability (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    IsProbabilityMeasure (tiltedProduct Q lam n) := by
  constructor
  rw [tiltedProduct, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (compact_integrable (continuous_normalizer n lam))
      (Filter.Eventually.of_forall (fun m ↦ (normalizer_positive (branchEdges_positive hl₀ hl₁ m)).le)),
    integral_normalizer]
  norm_num

lemma integral_tiltedProduct (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ)
    (f : (Fin n → Message) → ℝ) :
    (∫ m, f m ∂tiltedProduct Q lam n) =
      ∫ m, normalizer (branchEdges lam m)*f m ∂(Measure.pi fun _ ↦ Q.probability.toMeasure) := by
  rw [tiltedProduct, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun m : Fin n → Message ↦ ENNReal.ofReal (normalizer (branchEdges lam m))) from
      ENNReal.measurable_ofReal.comp (continuous_normalizer n lam).measurable)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  congr 1; funext m
  rw [ENNReal.toReal_ofReal (normalizer_positive (branchEdges_positive hl₀ hl₁ m)).le]
  rfl

lemma measurePreserving_density {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {T : X → X} (hT : MeasurePreserving T μ μ) {w : X → ENNReal} (hw : Measurable w)
    (hinv : ∀ x, w (T x) = w x) :
    MeasurePreserving T (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hT.measurable, Measure.ext (fun s hs ↦ ?_)⟩
  rw [Measure.map_apply hT.measurable hs, withDensity_apply _ (hT.measurable hs), withDensity_apply _ hs]
  have h := hT.setLIntegral_comp_preimage hs hw
  simpa only [hinv] using h

lemma branchProduct_permute {n : ℕ} (lam : ℝ) (σ : Equiv.Perm (Fin 3))
    (m : Fin n → Message) (i : Fin 3) :
    branchProduct (branchEdges lam (fun j ↦ permute σ (m j))) i =
      branchProduct (branchEdges lam m) (σ i) := rfl

lemma normalizer_permute {n : ℕ} (lam : ℝ) (σ : Equiv.Perm (Fin 3)) (m : Fin n → Message) :
    normalizer (branchEdges lam (fun j ↦ permute σ (m j))) = normalizer (branchEdges lam m) := by
  unfold normalizer
  change avg (fun i ↦ branchProduct (branchEdges lam m) (σ i)) = _
  exact avg_permute_vec σ (branchProduct (branchEdges lam m))

lemma branchOutput_permute {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) {n : ℕ}
    (σ : Equiv.Perm (Fin 3)) (m : Fin n → Message) :
    branchOutput hl₀ hl₁ (fun j ↦ permute σ (m j)) = permute σ (branchOutput hl₀ hl₁ m) := by
  apply Subtype.ext; funext i
  change branchProduct (branchEdges lam (fun j ↦ permute σ (m j))) i /
    normalizer (branchEdges lam (fun j ↦ permute σ (m j))) =
    branchProduct (branchEdges lam m) (σ i) / normalizer (branchEdges lam m)
  rw [branchProduct_permute, normalizer_permute]

lemma tiltedProduct_symmetric (Q : Law) {lam : ℝ} (_hl₀ : 0 ≤ lam) (_hl₁ : lam < 1) (n : ℕ)
    (σ : Equiv.Perm (Fin 3)) :
    MeasurePreserving (fun m : Fin n → Message ↦ fun j ↦ permute σ (m j))
      (tiltedProduct Q lam n) (tiltedProduct Q lam n) := by
  apply measurePreserving_density
    (measurePreserving_pi (fun _ ↦ Q.probability.toMeasure) (fun _ ↦ Q.probability.toMeasure)
      (fun _ ↦ Q.symmetric σ))
    (ENNReal.measurable_ofReal.comp (continuous_normalizer n lam).measurable)
  intro m
  change ENNReal.ofReal (normalizer (branchEdges lam (fun j ↦ permute σ (m j)))) = _
  rw [normalizer_permute]
  rfl

def finiteProbability (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    ProbabilityMeasure Message := by
  let ν : ProbabilityMeasure (Fin n → Message) := ⟨tiltedProduct Q lam n, tiltedProduct_isProbability Q hl₀ hl₁ n⟩
  exact ν.map (branchOutput hl₀ hl₁)

lemma integral_finiteProbability (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ)
    {f : Message → ℝ} (hf : Measurable f) :
    (∫ m, f m ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) =
      ∫ m : Fin n → Message, normalizer (branchEdges lam m)*f (branchOutput hl₀ hl₁ m)
        ∂(Measure.pi fun _ ↦ Q.probability.toMeasure) := by
  change (∫ m, f m ∂Measure.map (branchOutput hl₀ hl₁) (tiltedProduct Q lam n)) = _
  rw [integral_map (continuous_branchOutput hl₀ hl₁ n).measurable.aemeasurable hf.aestronglyMeasurable,
    integral_tiltedProduct Q hl₀ hl₁]

lemma finiteProbability_balanced (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) (i : Fin 3) :
    (∫ m, m.1 i ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) = 1 := by
  rw [integral_finiteProbability Q hl₀ hl₁ n (continuous_coordinate i).measurable]
  have he (m : Fin n → Message) :
      normalizer (branchEdges lam m)*(branchOutput hl₀ hl₁ m).1 i = branchProduct (branchEdges lam m) i := by
    change normalizer (branchEdges lam m)*(branchProduct (branchEdges lam m) i/normalizer (branchEdges lam m)) = _
    field_simp [ne_of_gt (normalizer_positive (branchEdges_positive hl₀ hl₁ m))]
  simp_rw [he]
  change (∫ m : Fin n → Message, ∏ j, edgeMessage lam (m j) i ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) = _
  rw [integral_fintype_prod_eq_pow (fun m : Message ↦ edgeMessage lam m i), Q.edge_balanced]
  simp

lemma finiteProbability_symmetric (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ)
    (σ : Equiv.Perm (Fin 3)) :
    MeasurePreserving (permute σ) (finiteProbability Q hl₀ hl₁ n).toMeasure
      (finiteProbability Q hl₀ hl₁ n).toMeasure := by
  refine ⟨(continuous_permute σ).measurable, ?_⟩
  change Measure.map (permute σ) (Measure.map (branchOutput hl₀ hl₁) (tiltedProduct Q lam n)) =
    Measure.map (branchOutput hl₀ hl₁) (tiltedProduct Q lam n)
  rw [Measure.map_map (continuous_permute σ).measurable (continuous_branchOutput hl₀ hl₁ n).measurable]
  have he : permute σ ∘ branchOutput hl₀ hl₁ =
      branchOutput hl₀ hl₁ ∘ (fun m : Fin n → Message ↦ fun j ↦ permute σ (m j)) := by
    funext m; exact (branchOutput_permute hl₀ hl₁ σ m).symm
  rw [he, ← Measure.map_map (continuous_branchOutput hl₀ hl₁ n).measurable
    (tiltedProduct_symmetric Q hl₀ hl₁ n σ).measurable,
    (tiltedProduct_symmetric Q hl₀ hl₁ n σ).map_eq]

def finiteLaw (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) : Law where
  probability := finiteProbability Q hl₀ hl₁ n
  balanced := finiteProbability_balanced Q hl₀ hl₁ n
  symmetric := finiteProbability_symmetric Q hl₀ hl₁ n

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {α : Type*}

lemma channel_real {lam : ℝ} (hlam : Admissible lam) (i j : Spin) :
    (channel lam hlam i j).toReal = channelWeight lam i j := by
  exact ENNReal.toReal_ofReal (channelWeight_nonneg hlam i j)

lemma edge_pmf_real {lam : ℝ} (hlam : Admissible lam) (p : Spin → PMF α) (i : Spin) (a : α) :
    (((channel lam hlam i).bind p) a).toReal =
      discreteWeight p a*edgeMessage lam (discreteMessage p a) i := by
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun j _ ↦ ENNReal.mul_ne_top ((channel lam hlam i).apply_ne_top j) ((p j).apply_ne_top a))]
  simp only [ENNReal.toReal_mul, channel_real]
  have he : discreteWeight p a*edgeMessage lam (discreteMessage p a) i =
      lam*(p i a).toReal+(1-lam)*discreteWeight p a := by
    dsimp only [edgeMessage, edge, centered]
    calc
      _ = lam*(discreteWeight p a*(discreteMessage p a : Spin → ℝ) i) +
          (1-lam)*discreteWeight p a := by ring
      _ = _ := by rw [discrete_bayes]
  rw [he]
  fin_cases i <;> simp [Fin.sum_univ_three, channelWeight, discreteWeight, avg] <;> ring

def discreteBranchLaw (p : Spin → PMF α) (lam : ℝ) (hlam : Admissible lam) (n : ℕ) (i : Spin) :
    PMF (Fin n → α) := productPMF (fun _ ↦ (channel lam hlam i).bind p)

lemma discreteBranchLaw_real (p : Spin → PMF α) {lam : ℝ} (hlam : Admissible lam)
    (n : ℕ) (i : Spin) (v : Fin n → α) :
    (discreteBranchLaw p lam hlam n i v).toReal =
      (∏ j, discreteWeight p (v j))*branchProduct (branchEdges lam (fun j ↦ discreteMessage p (v j))) i := by
  simp only [discreteBranchLaw, productPMF_apply, ENNReal.toReal_prod, edge_pmf_real,
    Finset.prod_mul_distrib, branchProduct, branchEdges]

lemma discreteBranchWeight (p : Spin → PMF α) {lam : ℝ} (hlam : Admissible lam)
    (n : ℕ) (v : Fin n → α) :
    discreteWeight (discreteBranchLaw p lam hlam n) v =
      (∏ j, discreteWeight p (v j))*normalizer (branchEdges lam (fun j ↦ discreteMessage p (v j))) := by
  unfold discreteWeight
  simp only [discreteBranchLaw_real]
  exact avg_mul _ _

lemma discreteBranchMessage (p : Spin → PMF α) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hlam : Admissible lam) (n : ℕ) (v : Fin n → α) (hv : (∏ j, discreteWeight p (v j)) ≠ 0) :
    discreteMessage (discreteBranchLaw p lam hlam n) v =
      branchOutput hl₀ hl₁ (fun j ↦ discreteMessage p (v j)) := by
  have hz := normalizer_positive (branchEdges_positive hl₀ hl₁ (fun j ↦ discreteMessage p (v j)))
  have hw : discreteWeight (discreteBranchLaw p lam hlam n) v ≠ 0 := by
    rw [discreteBranchWeight]; exact mul_ne_zero hv (ne_of_gt hz)
  apply Subtype.ext
  funext i
  rw [discrete_coord hw, discreteBranchLaw_real, discreteBranchWeight]
  change _ = branchProduct (branchEdges lam (fun j ↦ discreteMessage p (v j))) i /
    normalizer (branchEdges lam (fun j ↦ discreteMessage p (v j)))
  exact mul_div_mul_left _ _ hv

lemma discreteBranch_integrand (p : Spin → PMF α) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hlam : Admissible lam) (n : ℕ) (v : Fin n → α) (f : Message → ℝ) :
    discreteWeight (discreteBranchLaw p lam hlam n) v*f (discreteMessage (discreteBranchLaw p lam hlam n) v) =
      (∏ j, discreteWeight p (v j))*
        (normalizer (branchEdges lam (fun j ↦ discreteMessage p (v j)))*
          f (branchOutput hl₀ hl₁ (fun j ↦ discreteMessage p (v j)))) := by
  rw [discreteBranchWeight]
  by_cases hv : (∏ j, discreteWeight p (v j)) = 0
  · simp [hv]
  · rw [discreteBranchMessage p hl₀ hl₁ hlam n v hv, mul_assoc]

section Measures
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma discreteMessage_preserving (p : Spin → PMF α) :
    MeasurePreserving (discreteMessage p) (discreteMarginal p).toMeasure (discreteProbability p).toMeasure :=
  ⟨measurable_of_countable _, rfl⟩

lemma integral_discreteBranchLaw (p : Spin → PMF α) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hlam : Admissible lam) (n : ℕ) {f : Message → ℝ} (hf : Continuous f) :
    (∫ m, f m ∂(discreteProbability (discreteBranchLaw p lam hlam n)).toMeasure) =
      ∫ m : Fin n → Message, normalizer (branchEdges lam m)*f (branchOutput hl₀ hl₁ m)
        ∂(Measure.pi fun _ ↦ (discreteProbability p).toMeasure) := by
  let g : (Fin n → Message) → ℝ := fun m ↦ normalizer (branchEdges lam m)*f (branchOutput hl₀ hl₁ m)
  have hg : Continuous g := (continuous_normalizer n lam).mul (hf.comp (continuous_branchOutput hl₀ hl₁ n))
  have hp := measurePreserving_pi (fun _ : Fin n ↦ (discreteMarginal p).toMeasure)
    (fun _ : Fin n ↦ (discreteProbability p).toMeasure) (fun _ ↦ discreteMessage_preserving p)
  conv_rhs => rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hg.measurable.aestronglyMeasurable]
  rw [integral_discreteProbability _ hf.measurable, ← productPMF_measure]
  rw [PMF.integral_eq_tsum, PMF.integral_eq_tsum]
  · apply tsum_congr
    intro v
    simp only [smul_eq_mul, productPMF_apply, ENNReal.toReal_prod, discreteMarginal_real]
    exact discreteBranch_integrand p hl₀ hl₁ hlam n v f
  · rw [productPMF_measure]
    exact hp.integrable_comp_of_integrable (compact_integrable hg)
  · exact (discreteMessage_preserving _).integrable_comp_of_integrable (compact_integrable hf)

lemma probability_ext_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {P Q : ProbabilityMeasure X}
    (h : ∀ (f : X → ℝ), Continuous f → (∫ x, f x ∂P.toMeasure) = ∫ x, f x ∂Q.toMeasure) : P = Q := by
  apply Subtype.ext
  exact congrArg FiniteMeasure.toMeasure (FiniteMeasure.ext_of_forall_integral_eq
    (μ := P.toFiniteMeasure) (ν := Q.toFiniteMeasure) (fun f ↦ h f f.continuous))

lemma discreteBranchLaw_probability (p : Spin → PMF α) (Q : Law)
    (hQ : Q.probability = discreteProbability p) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hlam : Admissible lam) (n : ℕ) :
    discreteProbability (discreteBranchLaw p lam hlam n) = finiteProbability Q hl₀ hl₁ n := by
  apply probability_ext_continuous
  intro f hf
  rw [integral_discreteBranchLaw p hl₀ hl₁ hlam n hf,
    integral_finiteProbability Q hl₀ hl₁ n hf.measurable, hQ]

end Measures

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma measurable_symEntropy : Measurable (fun m : Message ↦ symEntropy m.1) := by
  have h (i : Fin 3) : Measurable (fun m : Message ↦ (m.1 i-1)*Real.log (m.1 i)) :=
    ((continuous_coordinate i).measurable.sub measurable_const).mul
      (Real.measurable_log.comp (continuous_coordinate i).measurable)
  exact (((h 0).add (h 1)).add (h 2)).div_const 3 |>.div_const 2

lemma measurable_info : Measurable (fun m : Message ↦ info m.1) := by
  have h (i : Fin 3) : Measurable (fun m : Message ↦ m.1 i*Real.log (m.1 i)) :=
    (continuous_coordinate i).measurable.mul (Real.measurable_log.comp (continuous_coordinate i).measurable)
  exact (((h 0).add (h 1)).add (h 2)).div_const 3

lemma measurable_correction : Measurable (fun m : Message ↦ correction m.1) := by
  have hl (i : Fin 3) : Measurable (fun m : Message ↦ Real.log (m.1 i)) :=
    Real.measurable_log.comp (continuous_coordinate i).measurable
  have hu (i : Fin 3) : Measurable (fun m : Message ↦ logCentered m.1 i) :=
    (hl i).sub ((((hl 0).add (hl 1)).add (hl 2)).div_const 3)
  have h (i : Fin 3) : Measurable (fun m : Message ↦ m.1 i*logCentered m.1 i^2) :=
    (continuous_coordinate i).measurable.mul ((hu i).pow_const 2)
  exact (((h 0).add (h 1)).add (h 2)).div_const 3 |>.div_const 2

lemma continuous_symEntropy_comp {X : Type*} [TopologicalSpace X] {f : X → Vec}
    (hf : Continuous f) (hp : ∀ x i, 0 < f x i) : Continuous (fun x ↦ symEntropy (f x)) := by
  unfold symEntropy
  exact (continuous_avg.comp (continuous_pi (fun i ↦
    (((continuous_apply i).comp hf).sub continuous_const).mul
      (((continuous_apply i).comp hf).log (fun x ↦ ne_of_gt (hp x i)))))).div_const 2

lemma continuous_correction_comp {X : Type*} [TopologicalSpace X] {f : X → Vec}
    (hf : Continuous f) (hp : ∀ x i, 0 < f x i) : Continuous (fun x ↦ correction (f x)) := by
  have hl (i : Fin 3) : Continuous (fun x ↦ Real.log (f x i)) :=
    ((continuous_apply i).comp hf).log (fun x ↦ ne_of_gt (hp x i))
  have hu (i : Fin 3) : Continuous (fun x ↦ logCentered (f x) i) :=
    (hl i).sub (continuous_avg.comp (continuous_pi hl))
  exact (continuous_avg.comp (continuous_pi (fun i ↦
    ((continuous_apply i).comp hf).mul ((hu i).pow 2)))).div_const 2

lemma continuous_info_comp {X : Type*} [TopologicalSpace X] {f : X → Vec}
    (hf : Continuous f) : Continuous (fun x ↦ info (f x)) :=
  continuous_avg.comp (continuous_pi (fun i ↦ Real.continuous_mul_log.comp ((continuous_apply i).comp hf)))

lemma finite_integrable_of_comp (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ)
    {f : Message → ℝ} (hf : Measurable f) (hc : Continuous (fun m : Fin n → Message ↦ f (branchOutput hl₀ hl₁ m))) :
    Integrable f (finiteProbability Q hl₀ hl₁ n).toMeasure := by
  have := tiltedProduct_isProbability Q hl₀ hl₁ n
  change Integrable f (Measure.map (branchOutput hl₀ hl₁) (tiltedProduct Q lam n))
  exact (integrable_map_measure hf.aestronglyMeasurable
    (continuous_branchOutput hl₀ hl₁ n).measurable.aemeasurable).2 (compact_integrable hc)

lemma finite_integrable_symEntropy (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    Integrable (fun m : Message ↦ symEntropy m.1) (finiteProbability Q hl₀ hl₁ n).toMeasure :=
  finite_integrable_of_comp Q hl₀ hl₁ n measurable_symEntropy
    (continuous_symEntropy_comp (continuous_subtype_val.comp (continuous_branchOutput hl₀ hl₁ n))
      (fun m i ↦ (normalizedProduct_positive (branchEdges_positive hl₀ hl₁ m)).1 i))

lemma finite_integrable_correction (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    Integrable (fun m : Message ↦ correction m.1) (finiteProbability Q hl₀ hl₁ n).toMeasure :=
  finite_integrable_of_comp Q hl₀ hl₁ n measurable_correction
    (continuous_correction_comp (continuous_subtype_val.comp (continuous_branchOutput hl₀ hl₁ n))
      (fun m i ↦ (normalizedProduct_positive (branchEdges_positive hl₀ hl₁ m)).1 i))

lemma measurableSet_positive : MeasurableSet {m : Message | PositiveMessage m.1} := by
  have he : {m : Message | PositiveMessage m.1} = {m : Message | ∀ i, 0 < m.1 i} := by
    ext m; exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, m.2.2⟩⟩
  rw [he]
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const (continuous_coordinate i).measurable)

lemma finite_positive (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    ∀ᵐ m ∂(finiteProbability Q hl₀ hl₁ n).toMeasure, PositiveMessage m.1 := by
  change ∀ᵐ m ∂Measure.map (branchOutput hl₀ hl₁) (tiltedProduct Q lam n), PositiveMessage m.1
  rw [ae_map_iff (continuous_branchOutput hl₀ hl₁ n).measurable.aemeasurable measurableSet_positive]
  exact Filter.Eventually.of_forall (fun m ↦ normalizedProduct_positive (branchEdges_positive hl₀ hl₁ m))

lemma finiteLaw_symEntropy (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    (∫ m, symEntropy m.1 ∂(finiteLaw Q hl₀ hl₁ n).probability.toMeasure) =
      n*(∫ m, symEntropy (edgeMessage lam m) ∂Q.probability.toMeasure) := by
  change (∫ m, symEntropy m.1 ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) = _
  rw [integral_finiteProbability Q hl₀ hl₁ n measurable_symEntropy]
  exact finite_symEntropy Q hl₀ hl₁ n

lemma finiteLaw_correction (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    (∫ m, correction m.1 ∂(finiteLaw Q hl₀ hl₁ n).probability.toMeasure) =
      n*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)+
      2*((n:ℝ)^2-n)*(∫ m, symEntropy (edgeMessage lam m) ∂Q.probability.toMeasure)^2 := by
  change (∫ m, correction m.1 ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) = _
  rw [integral_finiteProbability Q hl₀ hl₁ n measurable_correction]
  exact finite_correction Q hl₀ hl₁ n

lemma finiteLaw_info (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    (∫ m, info m.1 ∂(finiteLaw Q hl₀ hl₁ n).probability.toMeasure) =
      n*(∫ m, info (edgeMessage lam m) ∂Q.probability.toMeasure)-correlationEntropy Q lam n := by
  change (∫ m, info m.1 ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) = _
  rw [integral_finiteProbability Q hl₀ hl₁ n measurable_info]
  exact finite_info Q hl₀ hl₁ n

end ThreeState.TreeClauses.Experiment

end

end OAI
