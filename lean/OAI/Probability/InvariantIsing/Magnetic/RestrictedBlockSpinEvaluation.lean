import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinEvaluation
import OAI.Probability.InvariantIsing.Cavity.CavityReplicaLinearity

namespace OAI

/-! The constrained cavity spin test is exactly the integral against the
original constrained block overlap path. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma integrable_fieldLevelIndex (h : FieldStep) (f : Fin (h.depth + 1) → ℝ) :
    Integrable (fun s => f (fieldLevelIndex h s)) pathMeasure := by
  apply integrable_of_measurable_abs_le
    ((measurable_of_finite f).comp (fieldLevelIndex_monotone h).measurable)
    (c := ∑ i, |f i|)
  intro s
  exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ _)

def restrictedFieldBlockSpinIntegrand {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) : ℝ :=
  referenceReplicaMean
    ((restrictedSpinPrior S hS : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth => fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        ((N : ℝ)⁻¹ * ∑ j, spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))

def restrictedFieldBlockSpinMean {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (z : Fin N → ℝ) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) : ℝ :=
  ∫ p, restrictedFieldBlockSpinIntegrand S hS h z p q Φ ∂fieldVectorCoordinateLaw N h

lemma restrictedFieldBlockSpinIntegrand_eq_sum {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    restrictedFieldBlockSpinIntegrand S hS h z p q Φ =
      (N : ℝ)⁻¹ * ∑ j, restrictedFieldSpinPairIntegrand S hS h z p q Φ j := by
  let F := fun (j : Fin N) (σ : Fin 2 → Spin N × LabeledLeaf h.depth) =>
    Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
      (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))
  have hm : ∀ j, Measurable (F j) := fun _ => measurable_of_countable _
  have hb : ∀ j σ, |F j σ| ≤ C := by
    intro j σ
    simpa only [F, abs_mul, abs_spinValue, mul_one, one_mul] using hΦ _
  have he : (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        ((N : ℝ)⁻¹ * ∑ j, spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))) =
      (fun σ => (N : ℝ)⁻¹ * ∑ j, F j σ) := by
    funext σ
    dsimp only [F]
    rw [← Finset.mul_sum]
    ring
  unfold restrictedFieldBlockSpinIntegrand
  rw [he, referenceReplicaMean_const_mul, cavity_referenceReplicaMean_sum _ _ F hm (fun _ => C) hb]
  rfl

lemma restrictedFieldBlockSpinMean_eq_sum {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (z : Fin N → ℝ) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    restrictedFieldBlockSpinMean S hS h z q Φ =
      (N : ℝ)⁻¹ * ∑ j, restrictedFieldSpinPairMean S hS h z q Φ j := by
  unfold restrictedFieldBlockSpinMean
  simp_rw [restrictedFieldBlockSpinIntegrand_eq_sum S hS h z _ q Φ hΦ]
  have hi (j : Fin N) : Integrable (fun p => restrictedFieldSpinPairIntegrand S hS h z p q Φ j)
      (fieldVectorCoordinateLaw N h) := by
    have hp : Measurable (fun p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ) =>
        (z, p)) := measurable_const.prodMk measurable_id
    have hm0 := (measurable_restrictedFieldSpinPairIntegrand S hS h q Φ j).comp hp
    dsimp only [Function.comp_def] at hm0
    have hm : Measurable (fun p => restrictedFieldSpinPairIntegrand S hS h z p q Φ j) := hm0
    exact integrable_of_measurable_abs_le hm
      (fun p => restrictedFieldSpinPairIntegrand_abs_le S hS h q Φ j hΦ z p)
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
  rfl

theorem restricted_field_block_spin_evaluation
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    (∫ z, restrictedFieldBlockSpinMean S hS h z q Φ
      ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
      ∫ s, Φ (q (fieldLevelIndex h s)) * restrictedBlockOverlapPath hN S hS h s ∂pathMeasure := by
  simp_rw [restrictedFieldBlockSpinMean_eq_sum S hS h _ q Φ hΦ]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
    integrable_of_measurable_abs_le (measurable_restrictedFieldSpinPairMean S hS h q Φ j)
      (fun z => restrictedFieldSpinPairMean_abs_le S hS h q Φ j hΦ z))]
  simp_rw [restricted_field_spin_pair_evaluation hpub hN S hS h q Φ _ hΦ]
  let a := fun (j : Fin N) (i : Fin (h.depth + 1)) => Φ (q i) *
    (∫ z, restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut)
      (fieldStepVariance h)
      (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1)
      i j z ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)))
  change (N : ℝ)⁻¹ * (∑ j, ∫ s, a j (fieldLevelIndex h s) ∂pathMeasure) = _
  have hi (j : Fin N) : Integrable (fun s => a j (fieldLevelIndex h s)) pathMeasure :=
    integrable_fieldLevelIndex h (a j)
  rw [← integral_finsetSum _ (fun j _ => hi j), ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  dsimp only [a]
  change _ = Φ (q (fieldLevelIndex h s)) *
    restrictedBlockPairMean hN S hS h (fun _ => 0) (fieldLevelIndex h s)
  rw [restrictedBlockPairMean_eq_average]
  rw [← Finset.mul_sum]
  simp only [vectorGaussianLaw, ProbabilityMeasure.coe_mk]
  ring

end InvariantIsing

end

end OAI
