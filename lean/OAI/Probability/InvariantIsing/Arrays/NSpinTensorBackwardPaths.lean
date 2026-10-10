import OAI.Probability.InvariantIsing.Arrays.NSpinTensorBackwardDerivative

namespace OAI

/-! Collapse the two independent residual paths to actual backward gradients. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

def tensorPairCoordinatePayoff {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (q : ℕ) (z₁ z₂ : SpinTensorIndex I degree → ℝ) (j₁ j₂ : SpinTensorIndex I degree)
    (w : Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) : ℝ :=
  tensorTerminalCoordinateMean eig U c I degree amplitude (z₁ + ∑ i, (w i).1) j₁ *
    tensorTerminalCoordinateMean eig U c I degree amplitude (z₂ + ∑ i, (w i).2) j₂

lemma tensorPairCoordinatePayoff_cons {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (q : ℕ) (z₁ z₂ a₁ a₂ : SpinTensorIndex I degree → ℝ) (j₁ j₂ : SpinTensorIndex I degree)
    (w : Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) :
    tensorPairCoordinatePayoff eig U c I degree amplitude (q + 1) z₁ z₂ j₁ j₂ (Fin.cons (a₁, a₂) w) =
      tensorPairCoordinatePayoff eig U c I degree amplitude q (z₁ + a₁) (z₂ + a₂) j₁ j₂ w := by
  simp only [tensorPairCoordinatePayoff, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]

lemma tensorPairCoordinatePayoff_abs_le {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (q : ℕ) (z₁ z₂ : SpinTensorIndex I degree → ℝ) (j₁ j₂ : SpinTensorIndex I degree)
    (w : Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) :
    |tensorPairCoordinatePayoff eig U c I degree amplitude q z₁ z₂ j₁ j₂ w| ≤
      tensorFeatureCoordinateCap U I degree amplitude j₁ * tensorFeatureCoordinateCap U I degree amplitude j₂ := by
  rw [tensorPairCoordinatePayoff, abs_mul]
  exact mul_le_mul (tensorTerminalCoordinateMean_abs_le eig U c I degree amplitude _ j₁)
    (tensorTerminalCoordinateMean_abs_le eig U c I degree amplitude _ j₂) (abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- Once the two paths have branched, each terminal gradient averages
independently to its actual backward gradient. -/
theorem tensorAncestorPairPathMean_independent_coordinates {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (d q i : ℕ) (hqi : i + q = n) (hdi : d ≤ i)
    (z₁ z₂ : SpinTensorIndex I degree → ℝ) (j₁ j₂ : SpinTensorIndex I degree) :
    tensorAncestorPairPathMean eig U c I degree amplitude n b v d q i z₁ z₂
      (tensorPairCoordinatePayoff eig U c I degree amplitude q z₁ z₂ j₁ j₂) =
      tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z₁ j₁ *
        tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z₂ j₂ := by
  induction q generalizing i z₁ z₂ with
  | zero =>
    have hi : i = n := by omega
    subst i
    simp only [tensorAncestorPairPathMean, tensorPairCoordinatePayoff, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero, tensorBackwardCoordinateMean, Nat.sub_self, tensorCascadeCoordinateMean]
  | succ q ih =>
    have hi : i < n := by omega
    have hqi' : i + 1 + q = n := by omega
    have hdi' : d ≤ i + 1 := by omega
    dsimp only [tensorAncestorPairPathMean]
    rw [ite_eq_right (by omega : ¬i < d)]
    calc
      _ = ∫ a₁, ∫ a₂,
          tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1) (z₁ + a₁) j₁ *
          tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1) (z₂ + a₂) j₂
          ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₂
          ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₁ := by
        apply integral_congr_ae
        apply ae_of_all
        intro a₁
        apply integral_congr_ae
        apply ae_of_all
        intro a₂
        dsimp only
        have hF : (fun w => tensorPairCoordinatePayoff eig U c I degree amplitude (q + 1)
            z₁ z₂ j₁ j₂ (Fin.cons (a₁, a₂) w)) =
            tensorPairCoordinatePayoff eig U c I degree amplitude q (z₁ + a₁) (z₂ + a₂) j₁ j₂ :=
          funext (tensorPairCoordinatePayoff_cons eig U c I degree amplitude q z₁ z₂ a₁ a₂ j₁ j₂)
        rw [hF]
        exact ih (i + 1) hqi' hdi' (z₁ + a₁) (z₂ + a₂)
      _ = (∫ a₁, tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1) (z₁ + a₁) j₁
            ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₁) *
          (∫ a₂, tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1) (z₂ + a₂) j₂
            ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₂) := by
        simp_rw [integral_const_mul]
        rw [integral_mul_const]
      _ = _ := by
        rw [← tensorBackwardCoordinateMean_step hN eig U c I degree amplitude n b v hb i hi z₁ j₁,
          ← tensorBackwardCoordinateMean_step hN eig U c I degree amplitude n b v hb i hi z₂ j₂]

/-- Only the shared ancestor increments remain after the independent
suffixes have been integrated. At the branching level the integrand is
the product of actual backward gradients. -/
def tensorSharedCoordinateProduct {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (d : ℕ)
    (j₁ j₂ : SpinTensorIndex I degree) :
    (q : ℕ) → ℕ → (SpinTensorIndex I degree → ℝ) → (SpinTensorIndex I degree → ℝ) → ℝ
  | 0, i, z₁, z₂ =>
      tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z₁ j₁ *
        tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z₂ j₂
  | q + 1, i, z₁, z₂ =>
      if i < d then
        ∫ a, tensorSharedCoordinateProduct eig U c I degree amplitude n b v d j₁ j₂ q
          (i + 1) (z₁ + a) (z₂ + a) ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₁
      else
        tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z₁ j₁ *
          tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z₂ j₂

lemma tensorSharedCoordinateProduct_nonneg {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (d : ℕ) (j : SpinTensorIndex I degree) (q i : ℕ) (z : SpinTensorIndex I degree → ℝ) :
    0 ≤ tensorSharedCoordinateProduct eig U c I degree amplitude n b v d j j q i z z := by
  induction q generalizing i z with
  | zero => exact mul_self_nonneg _
  | succ q ih =>
    dsimp only [tensorSharedCoordinateProduct]
    split_ifs
    · exact integral_nonneg fun a => ih (i + 1) (z + a)
    · exact mul_self_nonneg _

/-- The finite pair-path expectation is an expectation over the common
ancestor path of the backward gradient product at branching. -/
theorem tensorAncestorPairPathMean_coordinates {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (d q i : ℕ) (hqi : i + q = n)
    (z₁ z₂ : SpinTensorIndex I degree → ℝ) (j₁ j₂ : SpinTensorIndex I degree) :
    tensorAncestorPairPathMean eig U c I degree amplitude n b v d q i z₁ z₂
      (tensorPairCoordinatePayoff eig U c I degree amplitude q z₁ z₂ j₁ j₂) =
      tensorSharedCoordinateProduct eig U c I degree amplitude n b v d j₁ j₂ q i z₁ z₂ := by
  induction q generalizing i z₁ z₂ with
  | zero =>
    have hi : i = n := by omega
    subst i
    simp only [tensorAncestorPairPathMean, tensorPairCoordinatePayoff, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero, tensorSharedCoordinateProduct, tensorBackwardCoordinateMean,
      Nat.sub_self, tensorCascadeCoordinateMean]
  | succ q ih =>
    by_cases hid : i < d
    · dsimp only [tensorAncestorPairPathMean, tensorSharedCoordinateProduct]
      rw [ite_eq_left hid, ite_eq_left hid]
      apply integral_congr_ae
      apply ae_of_all
      intro a
      dsimp only
      have hF : (fun w => tensorPairCoordinatePayoff eig U c I degree amplitude (q + 1)
          z₁ z₂ j₁ j₂ (Fin.cons (a, a) w)) =
          tensorPairCoordinatePayoff eig U c I degree amplitude q (z₁ + a) (z₂ + a) j₁ j₂ :=
        funext (tensorPairCoordinatePayoff_cons eig U c I degree amplitude q z₁ z₂ a a j₁ j₂)
      rw [hF]
      exact ih (i + 1) (by omega) (z₁ + a) (z₂ + a)
    · rw [tensorSharedCoordinateProduct, ite_eq_right hid]
      exact tensorAncestorPairPathMean_independent_coordinates hN eig U c I degree amplitude
        n b v hb d (q + 1) i hqi (by omega) z₁ z₂ j₁ j₂

lemma tensorAncestorPairPathMean_const_mul {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (d q i : ℕ) (z₁ z₂ : SpinTensorIndex I degree → ℝ)
    (F : (Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) → ℝ) (C : ℝ) :
    tensorAncestorPairPathMean eig U c I degree amplitude n b v d q i z₁ z₂ (fun w => C * F w) =
      C * tensorAncestorPairPathMean eig U c I degree amplitude n b v d q i z₁ z₂ F := by
  induction q generalizing i z₁ z₂ with
  | zero => rfl
  | succ q ih =>
    dsimp only [tensorAncestorPairPathMean]
    split_ifs <;> simp_rw [ih, integral_const_mul]

lemma tensorPairPathSpinMean_features {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (j₁ j₂ : SpinTensorIndex I degree)
    (w : Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) :
    tensorPairPathSpinMean eig U c I degree amplitude n (z, w)
      (fun σ => spinTensorFeature U I degree amplitude (σ 0) j₁ *
        spinTensorFeature U I degree amplitude (σ 1) j₂) =
      tensorPairCoordinatePayoff eig U c I degree amplitude n z z j₁ j₂ w := by
  let μ := fun j : Fin 2 => gibbsProbability (uniformSpinPrior N : Measure (Spin N))
    (tensorSpinBaseEnergy eig U c I degree amplitude (tensorPairPathState I degree n (z, w) j))
  change (∫ σ : Fin 2 → Spin N, spinTensorFeature U I degree amplitude (σ 0) j₁ *
    spinTensorFeature U I degree amplitude (σ 1) j₂ ∂Measure.pi μ) = _
  have h := integral_fin_nat_prod_eq_prod (μ := μ)
    (fun j σ => spinTensorFeature U I degree amplitude σ (if j = 0 then j₁ else j₂))
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simpa only [Fin.prod_univ_two, ite_eq_left rfl, ite_true, ite_eq_right h10, μ,
    integral_uniformSpinGibbs_eq, tensorTerminalCoordinateMean, tensorPairCoordinatePayoff,
    tensorPairPathState] using h

/-- Actual finite tensor feature pair tests are expectations of backward
gradient products along the shared ancestor path. -/
theorem tensorFeaturePair_backward_identity (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ)
    (ψ : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B)
    (j₁ j₂ : SpinTensorIndex I degree) :
    tensorSpinPairAverage eig U c I degree amplitude n b v z ψ
      (fun σ => spinTensorFeature U I degree amplitude (σ 0) j₁ *
        spinTensorFeature U I degree amplitude (σ 1) j₂) =
      ∫ α : ℕ → LabeledLeaf n, ψ (labeledCommonDepth n (α 0) (α 1)) *
        tensorSharedCoordinateProduct eig U c I degree amplitude n b v
          (labeledCommonDepth n (α 0) (α 1)) j₁ j₂ n 0 z z ∂cascadeReplicaLaw n b := by
  have hf (σ : Spin N) (j : SpinTensorIndex I degree) :
      |spinTensorFeature U I degree amplitude σ j| ≤ tensorFeatureCoordinateCap U I degree amplitude j := by
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (spinTensorFeature U I degree amplitude τ j))
      (Finset.mem_univ σ)
  rw [tensorSpinPair_markov_identity hpub hN eig U c I degree amplitude n b v hb z ψ _ hB hψ
    (C := tensorFeatureCoordinateCap U I degree amplitude j₁ * tensorFeatureCoordinateCap U I degree amplitude j₂)
    (fun σ => by
      rw [abs_mul]
      exact mul_le_mul (hf (σ 0) j₁) (hf (σ 1) j₂) (abs_nonneg _)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _))]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  simp only [tensorPairSpinPathPayoff, tensorPairPathSpinMean_features]
  rw [tensorAncestorPairPathMean_const_mul,
    tensorAncestorPairPathMean_coordinates hN eig U c I degree amplitude n b v hb _ n 0 (by omega)]

theorem tensorFeaturePair_nonneg (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ)
    (ψ : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) (hψ0 : ∀ d, 0 ≤ ψ d)
    (j : SpinTensorIndex I degree) :
    0 ≤ tensorSpinPairAverage eig U c I degree amplitude n b v z ψ
      (fun σ => spinTensorFeature U I degree amplitude (σ 0) j *
        spinTensorFeature U I degree amplitude (σ 1) j) := by
  rw [tensorFeaturePair_backward_identity hpub hN eig U c I degree amplitude n b v hb z ψ hB hψ j j]
  exact integral_nonneg fun α => mul_nonneg (hψ0 _)
    (tensorSharedCoordinateProduct_nonneg eig U c I degree amplitude n b v _ j n 0 z)

end InvariantIsing

end

end OAI
