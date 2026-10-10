import OAI.Probability.InvariantIsing.Arrays.NSpinTensorPairConditioning
import OAI.Probability.InvariantIsing.Arrays.OverlapBounds

namespace OAI

/-! Actual bounded spin pair tests under the published marked-path law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal NNReal

namespace InvariantIsing

abbrev TensorPairPathData {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :=
  (SpinTensorIndex I degree → ℝ) ×
    (Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ))

def tensorPairPathState {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (p : TensorPairPathData I degree n) (j : Fin 2) :
    SpinTensorIndex I degree → ℝ :=
  p.1 + ∑ i, if j = 0 then (p.2 i).1 else (p.2 i).2

lemma measurable_tensorPairPathState {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (j : Fin 2) :
    Measurable (fun p => tensorPairPathState I degree n p j) := by
  have hm (i : Fin n) : Measurable (fun p : TensorPairPathData I degree n =>
      if j = 0 then (p.2 i).1 else (p.2 i).2) := by
    split_ifs
    · exact ((measurable_pi_apply i).comp measurable_snd).fst
    · exact ((measurable_pi_apply i).comp measurable_snd).snd
  exact measurable_fst.add (Finset.measurable_sum _ fun i _ => hm i)

private lemma measurable_tensorPairSpinMeasures {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) :
    Measurable (fun p : TensorPairPathData I degree n => Measure.pi (fun j : Fin 2 =>
      gibbsProbability (uniformSpinPrior N : Measure (Spin N))
        (tensorSpinBaseEnergy eig U c I degree amplitude (tensorPairPathState I degree n p j)))) := by
  have hν (j : Fin 2) : Measurable (fun p : TensorPairPathData I degree n =>
      gibbsProbability (uniformSpinPrior N : Measure (Spin N))
        (tensorSpinBaseEnergy eig U c I degree amplitude (tensorPairPathState I degree n p j))) := by
    let H : TensorPairPathData I degree n × Spin N → ℝ := fun p =>
      tensorSpinBaseEnergy eig U c I degree amplitude (tensorPairPathState I degree n p.1 j) p.2
    have hH : Measurable H := by
      apply measurable_from_prod_countable_left
      intro σ
      have hm := (measurable_pi_apply σ).comp
        ((measurable_spinTensorEnergyMark U I degree amplitude).comp
          (measurable_tensorPairPathState I degree n j))
      exact hm.const_add (rotatedEnergy eig U σ + fieldEnergy c σ)
    exact measurable_gibbsProbability
      (ν := fun _ : TensorPairPathData I degree n => (uniformSpinPrior N : Measure (Spin N)))
      (H := H) measurable_const hH
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (p : TensorPairPathData I degree n) :
      (Measure.pi (fun j : Fin 2 => gibbsProbability (uniformSpinPrior N : Measure (Spin N))
        (tensorSpinBaseEnergy eig U c I degree amplitude (tensorPairPathState I degree n p j)))) s =
      ∑' σ : Fin 2 → Spin N,
        (∏ j : Fin 2, gibbsProbability (uniformSpinPrior N : Measure (Spin N))
          (tensorSpinBaseEnergy eig U c I degree amplitude (tensorPairPathState I degree n p j)) {σ j}) *
          Measure.dirac σ s := by
    rw [← Measure.sum_smul_dirac (Measure.pi _), Measure.sum_apply _ hs]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_singleton]
  simp_rw [he]
  apply Measurable.tsum
  intro σ
  exact (Finset.measurable_prod _ fun j _ =>
    (Measure.measurable_coe (measurableSet_singleton _)).comp (hν j)).mul_const _

def tensorPairPathSpinKernel {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) : Kernel (TensorPairPathData I degree n) (Fin 2 → Spin N) :=
  ⟨fun p => Measure.pi (fun j : Fin 2 =>
    gibbsProbability (uniformSpinPrior N : Measure (Spin N))
      (tensorSpinBaseEnergy eig U c I degree amplitude (tensorPairPathState I degree n p j))),
    measurable_tensorPairSpinMeasures eig U c I degree amplitude n⟩

instance tensorPairPathSpinKernel_markov {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) : IsMarkovKernel (tensorPairPathSpinKernel eig U c I degree amplitude n) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

def tensorPairPathSpinMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (p : TensorPairPathData I degree n) (D : (Fin 2 → Spin N) → ℝ) : ℝ :=
  ∫ σ, D σ ∂tensorPairPathSpinKernel eig U c I degree amplitude n p

lemma measurable_tensorPairPathSpinMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (D : (Fin 2 → Spin N) → ℝ) :
    Measurable (fun p => tensorPairPathSpinMean eig U c I degree amplitude n p D) := by
  have hm : Measurable (fun p : TensorPairPathData I degree n × (Fin 2 → Spin N) => D p.2) :=
    (measurable_of_countable D).comp measurable_snd
  exact (hm.stronglyMeasurable.integral_kernel_prod_right'
    (κ := tensorPairPathSpinKernel eig U c I degree amplitude n)).measurable

lemma tensorPairPathSpinMean_abs_le {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (p : TensorPairPathData I degree n) (D : (Fin 2 → Spin N) → ℝ)
    {C : ℝ} (hD : ∀ σ, |D σ| ≤ C) :
    |tensorPairPathSpinMean eig U c I degree amplitude n p D| ≤ C :=
  abs_integral_le_const_of_bound (measurable_of_countable D) hD

def tensorPairSpinPathPayoff {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (ψ : ℕ → ℝ) (D : (Fin 2 → Spin N) → ℝ)
    (p : (SpinTensorIndex I degree → ℝ) ×
      (ℕ × (Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)))) : ℝ :=
  ψ p.2.1 * tensorPairPathSpinMean eig U c I degree amplitude n (p.1, p.2.2) D

lemma measurable_tensorPairSpinPathPayoff {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (ψ : ℕ → ℝ) (D : (Fin 2 → Spin N) → ℝ) :
    Measurable (tensorPairSpinPathPayoff eig U c I degree amplitude n ψ D) :=
  ((measurable_of_countable ψ).comp measurable_snd.fst).mul
    ((measurable_tensorPairPathSpinMean eig U c I degree amplitude n D).comp
      (measurable_fst.prodMk measurable_snd.snd))

lemma tensorPairSpinPathPayoff_abs_le {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (ψ : ℕ → ℝ) (D : (Fin 2 → Spin N) → ℝ)
    {B C : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) (hD : ∀ σ, |D σ| ≤ C)
    (p : (SpinTensorIndex I degree → ℝ) ×
      (ℕ × (Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)))) :
    |tensorPairSpinPathPayoff eig U c I degree amplitude n ψ D p| ≤ B * C := by
  rw [tensorPairSpinPathPayoff, abs_mul]
  exact mul_le_mul (hψ _) (tensorPairPathSpinMean_abs_le eig U c I degree amplitude n _ D hD)
    (abs_nonneg _) hB

private lemma tensorPairPathState_edges {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n)
    (α : Fin 2 → LabeledLeaf n) (j : Fin 2) :
    tensorPairPathState I degree n
      (z, fun i => (p.2 (edgeAt n (α 0) i), p.2 (edgeAt n (α 1) i))) j =
      labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) (α j) z := by
  funext a
  rw [labeledEnergy_edge_sum]
  fin_cases j <;> simp [tensorPairPathState, Pi.add_apply, Finset.sum_apply]

private lemma tensorPairPathSpinKernel_edges {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n)
    (α : Fin 2 → LabeledLeaf n) :
    tensorPairPathSpinKernel eig U c I degree amplitude n
      (z, fun i => (p.2 (edgeAt n (α 0) i), p.2 (edgeAt n (α 1) i))) =
      spinLeafPairResidualKernel (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) α := by
  change Measure.pi _ = Measure.pi _
  congr 1
  funext j
  rw [tensorPairPathState_edges]
  rfl

def tensorSpinPairAverage {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) (ψ : ℕ → ℝ) (D : (Fin 2 → Spin N) → ℝ) : ℝ :=
  ∫ p : TensorCoordinateData I degree n,
    referenceReplicaMean ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw n p.1))
      (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p)
      (fun x : Fin 2 → Spin N × LabeledLeaf n =>
        ψ (labeledCommonDepth n (x 0).2 (x 1).2) * D (fun j => (x j).1))
    ∂tensorCoordinateLaw I degree n b v

theorem tensorSpinPairAverage_eq_tiltedPath {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ)
    (ψ : ℕ → ℝ) (D : (Fin 2 → Spin N) → ℝ)
    {B C : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) (hD : ∀ σ, |D σ| ≤ C) :
    tensorSpinPairAverage eig U c I degree amplitude n b v z ψ D =
      tensorTiltedPairPathMean eig U c I degree amplitude n b v z
        (fun q => tensorPairSpinPathPayoff eig U c I degree amplitude n ψ D (z, q)) := by
  apply integral_congr_ae
  filter_upwards [tensorLeafSpinPair_conditioning_ae hN eig U c I degree amplitude n b v hb z] with p hp
  let D' := fun x : Fin 2 → Spin N × LabeledLeaf n =>
    ψ (labeledCommonDepth n (x 0).2 (x 1).2) * D (fun j => (x j).1)
  have hD' : ∀ x, |D' x| ≤ B * C := by
    intro x
    dsimp only [D']
    rw [abs_mul]
    exact mul_le_mul (hψ _) (hD _) (abs_nonneg _) hB
  rw [hp D' ⟨B * C, hD'⟩]
  congr 1
  funext α
  dsimp only [tensorPairSpinPathPayoff, tensorPairPathSpinMean]
  rw [tensorPairPathSpinKernel_edges]
  rw [← integral_const_mul]
  rfl

/-- The actual spin/leaf pair expectation is a Markov ancestor-path
expectation conditional only on the precise published cascade input. -/
theorem tensorSpinPair_markov_identity (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ)
    (ψ : ℕ → ℝ) (D : (Fin 2 → Spin N) → ℝ)
    {B C : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) (hD : ∀ σ, |D σ| ≤ C) :
    tensorSpinPairAverage eig U c I degree amplitude n b v z ψ D =
      ∫ α : ℕ → LabeledLeaf n,
        tensorAncestorPairPathMean eig U c I degree amplitude n b v
          (labeledCommonDepth n (α 0) (α 1)) n 0 z z
          (fun w => tensorPairSpinPathPayoff eig U c I degree amplitude n ψ D
            (z, labeledCommonDepth n (α 0) (α 1), w))
        ∂cascadeReplicaLaw n b := by
  rw [tensorSpinPairAverage_eq_tiltedPath hN eig U c I degree amplitude n b v hb z ψ D hB hψ hD]
  apply hpub N m k hN eig U c I degree amplitude n b v hb z
  · exact (measurable_tensorPairSpinPathPayoff eig U c I degree amplitude n ψ D).comp
      (measurable_const.prodMk measurable_id)
  · exact ⟨B * C, fun p => tensorPairSpinPathPayoff_abs_le eig U c I degree amplitude n ψ D hB hψ hD (z, p)⟩

theorem tensorProjectedOverlap_markov_identity (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ)
    (J : Finset (Fin N)) (ψ : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) :
    tensorSpinPairAverage eig U c I degree amplitude n b v z ψ
      (fun σ => projectedOverlap U J (σ 0) (σ 1)) =
      ∫ α : ℕ → LabeledLeaf n,
        tensorAncestorPairPathMean eig U c I degree amplitude n b v
          (labeledCommonDepth n (α 0) (α 1)) n 0 z z
          (fun w => tensorPairSpinPathPayoff eig U c I degree amplitude n ψ
            (fun σ => projectedOverlap U J (σ 0) (σ 1))
            (z, labeledCommonDepth n (α 0) (α 1), w))
        ∂cascadeReplicaLaw n b :=
  tensorSpinPair_markov_identity hpub hN eig U c I degree amplitude n b v hb z ψ _ hB hψ
    (fun σ => projectedOverlap_abs_le_one U J (σ 0) (σ 1))

/-- The root Gaussian retains its original law and is averaged after the
conditional spin/ancestor-path identity. -/
theorem tensorRootedSpinPair_markov_identity (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (ψ : ℕ → ℝ) (D : (Fin 2 → Spin N) → ℝ)
    {B C : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) (hD : ∀ σ, |D σ| ≤ C) :
    (∫ z, tensorSpinPairAverage eig U c I degree amplitude n b (fun i => v (i + 1)) z ψ D
      ∂(tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))) =
      ∫ z, ∫ α : ℕ → LabeledLeaf n,
        tensorAncestorPairPathMean eig U c I degree amplitude n b (fun i => v (i + 1))
          (labeledCommonDepth n (α 0) (α 1)) n 0 z z
          (fun w => tensorPairSpinPathPayoff eig U c I degree amplitude n ψ D
            (z, labeledCommonDepth n (α 0) (α 1), w))
        ∂cascadeReplicaLaw n b
      ∂(tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)) := by
  exact integral_congr_ae (ae_of_all _ fun z => tensorSpinPair_markov_identity hpub hN eig U c I degree
    amplitude n b (fun i => v (i + 1)) hb z ψ D hB hψ hD)

end InvariantIsing

end

end OAI
