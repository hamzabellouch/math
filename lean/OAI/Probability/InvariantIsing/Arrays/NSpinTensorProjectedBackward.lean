import OAI.Probability.InvariantIsing.Arrays.NSpinTensorBackwardPaths

namespace OAI

/-! Projected overlaps as products of actual backward site gradients. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

def rotationCoordinate {N : ℕ} (U : Rotation N) (a i : Fin N) : ℝ :=
  U (WithLp.toLp 2 (Pi.single i 1)) a

lemma rotation_apply_coordinates {N : ℕ} (U : Rotation N) (f : Fin N → ℝ) (a : Fin N) :
    U (WithLp.toLp 2 f) a = ∑ i, rotationCoordinate U a i * f i := by
  classical
  have hv : (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin N)) =
      ∑ i : Fin N, f i • (WithLp.toLp 2 (Pi.single i 1) : EuclideanSpace ℝ (Fin N)) := by
    ext j
    change f j = WithLp.ofLp (∑ i : Fin N, f i •
      (WithLp.toLp 2 (Pi.single i 1) : EuclideanSpace ℝ (Fin N))) j
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp [mul_ite]
  rw [hv, map_sum]
  change WithLp.ofLp (∑ i : Fin N, U (f i • WithLp.toLp 2 (Pi.single i 1))) a = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, rotationCoordinate, mul_comm]

def tensorBackwardProjectedMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (i : ℕ) (z : SpinTensorIndex I degree → ℝ) (a : Fin N) : ℝ :=
  ∑ s, rotationCoordinate U a s * tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z (Sum.inl s)

lemma tensorBackwardProjectedMean_eq {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (i : ℕ) (z : SpinTensorIndex I degree → ℝ) (a : Fin N) :
    tensorBackwardProjectedMean eig U c I degree amplitude n b v i z a =
      U (WithLp.toLp 2 (fun s => tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z (Sum.inl s))) a :=
  (rotation_apply_coordinates U _ a).symm

def tensorProjectedCoordinateCap {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (a : Fin N) : ℝ :=
  ∑ s, |rotationCoordinate U a s| * tensorFeatureCoordinateCap U I degree amplitude (Sum.inl s)

lemma measurable_tensorBackwardProjectedMean {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (a : Fin N) :
    Measurable (fun z => tensorBackwardProjectedMean eig U c I degree amplitude n b v i z a) :=
  Finset.measurable_sum _ fun s _ =>
    (measurable_tensorBackwardCoordinateMean hN eig U c I degree amplitude n b v hb i (Sum.inl s)).const_mul _

lemma tensorBackwardProjectedMean_abs_le {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (z : SpinTensorIndex I degree → ℝ) (a : Fin N) :
    |tensorBackwardProjectedMean eig U c I degree amplitude n b v i z a| ≤
      tensorProjectedCoordinateCap U I degree amplitude a := by
  unfold tensorBackwardProjectedMean tensorProjectedCoordinateCap
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (tensorBackwardCoordinateMean_abs_le hN eig U c I degree amplitude n b v hb i z (Sum.inl s)) (abs_nonneg _)

lemma integrable_tensorBackwardProjectedMean {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (z : SpinTensorIndex I degree → ℝ) (a : Fin N)
    (μ : Measure (SpinTensorIndex I degree → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun x => tensorBackwardProjectedMean eig U c I degree amplitude n b v i (z + x) a) μ :=
  Integrable.of_bound
    ((measurable_tensorBackwardProjectedMean hN eig U c I degree amplitude n b v hb i a).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable
    (tensorProjectedCoordinateCap U I degree amplitude a)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using
      tensorBackwardProjectedMean_abs_le hN eig U c I degree amplitude n b v hb i (z + x) a)

theorem tensorBackwardProjectedMean_step {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (hi : i < n)
    (z : SpinTensorIndex I degree → ℝ) (a : Fin N) :
    tensorBackwardProjectedMean eig U c I degree amplitude n b v i z a =
      ∫ x, tensorBackwardProjectedMean eig U c I degree amplitude n b v (i + 1) (z + x) a
        ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z := by
  let := tensorAncestorMarkKernel_markov hN eig U c I degree amplitude n b v hb i
  have hint (s : Fin N) : Integrable (fun x => rotationCoordinate U a s *
      tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1) (z + x) (Sum.inl s))
      (tensorAncestorMarkKernel eig U c I degree amplitude n b v i z) := by
    apply Integrable.const_mul
    apply Integrable.of_bound
      ((measurable_tensorBackwardCoordinateMean hN eig U c I degree amplitude n b v hb (i + 1) (Sum.inl s)).comp
        (measurable_const.add measurable_id)).aestronglyMeasurable
      (tensorFeatureCoordinateCap U I degree amplitude (Sum.inl s))
    exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.add_apply, id_eq] using
      tensorBackwardCoordinateMean_abs_le hN eig U c I degree amplitude n b v hb (i + 1) (z + x) (Sum.inl s)
  rw [tensorBackwardProjectedMean, show (fun x => tensorBackwardProjectedMean eig U c I degree amplitude n b v
      (i + 1) (z + x) a) = (fun x => ∑ s, rotationCoordinate U a s *
        tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1) (z + x) (Sum.inl s)) from rfl,
    integral_finsetSum _ (fun s _ => hint s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_const_mul, ← tensorBackwardCoordinateMean_step hN eig U c I degree amplitude n b v hb i hi z (Sum.inl s)]

lemma tensorBackwardProjectedMean_terminal {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) (a : Fin N) :
    tensorBackwardProjectedMean eig U c I degree amplitude n b v n z a =
      tensorProjectedMagnetization eig U c I degree amplitude z a := by
  rw [tensorBackwardProjectedMean_eq, tensorProjectedMagnetization_eq]
  simp only [tensorBackwardCoordinateMean, Nat.sub_self, tensorCascadeCoordinateMean]

def tensorProjectedPairPayoff {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (J : Finset (Fin N))
    (q : ℕ) (z₁ z₂ : SpinTensorIndex I degree → ℝ)
    (w : Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ a ∈ J,
    tensorBackwardProjectedMean eig U c I degree amplitude n b v n (z₁ + ∑ i, (w i).1) a *
      tensorBackwardProjectedMean eig U c I degree amplitude n b v n (z₂ + ∑ i, (w i).2) a

lemma tensorProjectedPairPayoff_cons {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (J : Finset (Fin N))
    (q : ℕ) (z₁ z₂ a₁ a₂ : SpinTensorIndex I degree → ℝ)
    (w : Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) :
    tensorProjectedPairPayoff eig U c I degree amplitude n b v J (q + 1) z₁ z₂ (Fin.cons (a₁, a₂) w) =
      tensorProjectedPairPayoff eig U c I degree amplitude n b v J q (z₁ + a₁) (z₂ + a₂) w := by
  simp only [tensorProjectedPairPayoff, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]

private lemma integral_pair_product_sum {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (J : Finset C) (F : C → A → ℝ) (G : C → B → ℝ)
    (hF : ∀ a ∈ J, Integrable (F a) μ) (hG : ∀ a ∈ J, Integrable (G a) ν) (c : ℝ) :
    (∫ x, ∫ y, c * ∑ a ∈ J, F a x * G a y ∂ν ∂μ) =
      c * ∑ a ∈ J, (∫ x, F a x ∂μ) * ∫ y, G a y ∂ν := by
  have hi (x : A) : (∫ y, c * ∑ a ∈ J, F a x * G a y ∂ν) =
      c * ∑ a ∈ J, F a x * ∫ y, G a y ∂ν := by
    rw [integral_const_mul, integral_finsetSum _ (fun a ha => (hG a ha).const_mul (F a x))]
    simp_rw [integral_const_mul]
  simp_rw [hi]
  rw [integral_const_mul, integral_finsetSum _ (fun a ha => (hF a ha).mul_const _)]
  simp_rw [integral_mul_const]

theorem tensorAncestorPairPathMean_independent_projected {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (J : Finset (Fin N)) (d q i : ℕ) (hqi : i + q = n) (hdi : d ≤ i)
    (z₁ z₂ : SpinTensorIndex I degree → ℝ) :
    tensorAncestorPairPathMean eig U c I degree amplitude n b v d q i z₁ z₂
      (tensorProjectedPairPayoff eig U c I degree amplitude n b v J q z₁ z₂) =
      (N : ℝ)⁻¹ * ∑ a ∈ J,
        tensorBackwardProjectedMean eig U c I degree amplitude n b v i z₁ a *
          tensorBackwardProjectedMean eig U c I degree amplitude n b v i z₂ a := by
  induction q generalizing i z₁ z₂ with
  | zero =>
    have hi : i = n := by omega
    subst i
    simp only [tensorAncestorPairPathMean, tensorProjectedPairPayoff, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero]
  | succ q ih =>
    have hi : i < n := by omega
    let := tensorAncestorMarkKernel_markov hN eig U c I degree amplitude n b v hb i
    dsimp only [tensorAncestorPairPathMean]
    rw [ite_eq_right (by omega : ¬i < d)]
    calc
      _ = ∫ x, ∫ y, (N : ℝ)⁻¹ * ∑ a ∈ J,
          tensorBackwardProjectedMean eig U c I degree amplitude n b v (i + 1) (z₁ + x) a *
            tensorBackwardProjectedMean eig U c I degree amplitude n b v (i + 1) (z₂ + y) a
          ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₂
          ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₁ := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        apply integral_congr_ae
        apply ae_of_all
        intro y
        dsimp only
        have hP : (fun w => tensorProjectedPairPayoff eig U c I degree amplitude n b v J (q + 1)
            z₁ z₂ (Fin.cons (x, y) w)) =
            tensorProjectedPairPayoff eig U c I degree amplitude n b v J q (z₁ + x) (z₂ + y) :=
          funext (tensorProjectedPairPayoff_cons eig U c I degree amplitude n b v J q z₁ z₂ x y)
        rw [hP]
        exact ih (i + 1) (by omega) (by omega) (z₁ + x) (z₂ + y)
      _ = _ := by
        rw [integral_pair_product_sum]
        · congr 1
          apply Finset.sum_congr rfl
          intro a ha
          rw [← tensorBackwardProjectedMean_step hN eig U c I degree amplitude n b v hb i hi z₁ a,
            ← tensorBackwardProjectedMean_step hN eig U c I degree amplitude n b v hb i hi z₂ a]
        · intro a _
          exact integrable_tensorBackwardProjectedMean hN eig U c I degree amplitude n b v hb (i + 1) z₁ a _
        · intro a _
          exact integrable_tensorBackwardProjectedMean hN eig U c I degree amplitude n b v hb (i + 1) z₂ a _

def tensorSharedProjectedProduct {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (J : Finset (Fin N)) (d : ℕ) :
    (q : ℕ) → ℕ → (SpinTensorIndex I degree → ℝ) → (SpinTensorIndex I degree → ℝ) → ℝ
  | 0, i, z₁, z₂ => (N : ℝ)⁻¹ * ∑ a ∈ J,
      tensorBackwardProjectedMean eig U c I degree amplitude n b v i z₁ a *
        tensorBackwardProjectedMean eig U c I degree amplitude n b v i z₂ a
  | q + 1, i, z₁, z₂ => if i < d then
      ∫ x, tensorSharedProjectedProduct eig U c I degree amplitude n b v J d q
        (i + 1) (z₁ + x) (z₂ + x) ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₁
    else (N : ℝ)⁻¹ * ∑ a ∈ J,
      tensorBackwardProjectedMean eig U c I degree amplitude n b v i z₁ a *
        tensorBackwardProjectedMean eig U c I degree amplitude n b v i z₂ a

lemma tensorSharedProjectedProduct_nonneg {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (J : Finset (Fin N)) (d q i : ℕ) (z : SpinTensorIndex I degree → ℝ) :
    0 ≤ tensorSharedProjectedProduct eig U c I degree amplitude n b v J d q i z z := by
  induction q generalizing i z with
  | zero => exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  | succ q ih =>
    dsimp only [tensorSharedProjectedProduct]
    split_ifs
    · exact integral_nonneg fun a => ih (i + 1) (z + a)
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

theorem tensorAncestorPairPathMean_projected {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (J : Finset (Fin N)) (d q i : ℕ) (hqi : i + q = n)
    (z₁ z₂ : SpinTensorIndex I degree → ℝ) :
    tensorAncestorPairPathMean eig U c I degree amplitude n b v d q i z₁ z₂
      (tensorProjectedPairPayoff eig U c I degree amplitude n b v J q z₁ z₂) =
      tensorSharedProjectedProduct eig U c I degree amplitude n b v J d q i z₁ z₂ := by
  induction q generalizing i z₁ z₂ with
  | zero =>
    have hi : i = n := by omega
    subst i
    simp only [tensorAncestorPairPathMean, tensorProjectedPairPayoff, tensorSharedProjectedProduct,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ q ih =>
    by_cases hid : i < d
    · dsimp only [tensorAncestorPairPathMean, tensorSharedProjectedProduct]
      rw [ite_eq_left hid, ite_eq_left hid]
      apply integral_congr_ae
      apply ae_of_all
      intro a
      dsimp only
      have hP : (fun w => tensorProjectedPairPayoff eig U c I degree amplitude n b v J (q + 1)
          z₁ z₂ (Fin.cons (a, a) w)) =
          tensorProjectedPairPayoff eig U c I degree amplitude n b v J q (z₁ + a) (z₂ + a) :=
        funext (tensorProjectedPairPayoff_cons eig U c I degree amplitude n b v J q z₁ z₂ a a)
      rw [hP]
      exact ih (i + 1) (by omega) (z₁ + a) (z₂ + a)
    · rw [tensorSharedProjectedProduct, ite_eq_right hid]
      exact tensorAncestorPairPathMean_independent_projected hN eig U c I degree amplitude
        n b v hb J d (q + 1) i hqi (by omega) z₁ z₂

lemma tensorPairPathSpinMean_projectedPayoff {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (J : Finset (Fin N)) (z : SpinTensorIndex I degree → ℝ)
    (w : Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) :
    tensorPairPathSpinMean eig U c I degree amplitude n (z, w)
      (fun σ => projectedOverlap U J (σ 0) (σ 1)) =
      tensorProjectedPairPayoff eig U c I degree amplitude n b v J n z z w := by
  rw [tensorPairPathSpinMean_overlap]
  simp only [tensorProjectedPairPayoff, tensorBackwardProjectedMean_terminal, tensorPairPathState,
    ite_true, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]

/-- The actual projected-overlap test is the shared-path expectation of
products of projected backward gradients at the branching level. -/
theorem tensorProjectedOverlap_backward_identity (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (J : Finset (Fin N)) (z : SpinTensorIndex I degree → ℝ)
    (ψ : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) :
    tensorSpinPairAverage eig U c I degree amplitude n b v z ψ
      (fun σ => projectedOverlap U J (σ 0) (σ 1)) =
      ∫ α : ℕ → LabeledLeaf n, ψ (labeledCommonDepth n (α 0) (α 1)) *
        tensorSharedProjectedProduct eig U c I degree amplitude n b v J
          (labeledCommonDepth n (α 0) (α 1)) n 0 z z ∂cascadeReplicaLaw n b := by
  rw [tensorProjectedOverlap_markov_identity hpub hN eig U c I degree amplitude n b v hb z J ψ hB hψ]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  simp only [tensorPairSpinPathPayoff,
    tensorPairPathSpinMean_projectedPayoff eig U c I degree amplitude n b v J z]
  rw [tensorAncestorPairPathMean_const_mul,
    tensorAncestorPairPathMean_projected hN eig U c I degree amplitude n b v hb J _ n 0 (by omega)]

theorem tensorProjectedOverlap_nonneg (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (J : Finset (Fin N)) (z : SpinTensorIndex I degree → ℝ)
    (ψ : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) (hψ0 : ∀ d, 0 ≤ ψ d) :
    0 ≤ tensorSpinPairAverage eig U c I degree amplitude n b v z ψ
      (fun σ => projectedOverlap U J (σ 0) (σ 1)) := by
  rw [tensorProjectedOverlap_backward_identity hpub hN eig U c I degree amplitude n b v hb J z ψ hB hψ]
  exact integral_nonneg fun α => mul_nonneg (hψ0 _)
    (tensorSharedProjectedProduct_nonneg eig U c I degree amplitude n b v J _ n 0 z)

theorem tensorRootedProjectedOverlap_backward_identity (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (J : Finset (Fin N))
    (ψ : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ d, |ψ d| ≤ B) :
    (∫ z, tensorSpinPairAverage eig U c I degree amplitude n b (fun i => v (i + 1)) z ψ
      (fun σ => projectedOverlap U J (σ 0) (σ 1))
      ∂(tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))) =
      ∫ z, ∫ α : ℕ → LabeledLeaf n, ψ (labeledCommonDepth n (α 0) (α 1)) *
        tensorSharedProjectedProduct eig U c I degree amplitude n b (fun i => v (i + 1)) J
          (labeledCommonDepth n (α 0) (α 1)) n 0 z z ∂cascadeReplicaLaw n b
          ∂(tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)) := by
  apply integral_congr_ae
  exact ae_of_all _ fun z => tensorProjectedOverlap_backward_identity hpub hN eig U c I degree amplitude
    n b (fun i => v (i + 1)) hb J z ψ hB hψ

end InvariantIsing

end

end OAI
