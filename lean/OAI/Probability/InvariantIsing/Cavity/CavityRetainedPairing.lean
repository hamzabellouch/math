import OAI.Probability.InvariantIsing.Cavity.CavitySpecialPythagoras
import OAI.Probability.InvariantIsing.Cavity.CavityOverlapError

namespace OAI

/-! Pairing identities for retained spectral directions and the
pointwise overlap error before taking any Gibbs average. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_masked_pairing_bound {d : ℕ} (I : Finset (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) :
    |∑ i ∈ I, x i * y i| ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  exact cavityCoordinatePairing_abs_le (LinearIsometryEquiv.refl ℝ _) I x y

lemma cavity_spectral_pairing_decomposition {r m n k : ℕ}
    (g : Fin r → Fin m) (a : Fin m)
    (R : Matrix (Fin r) (Fin k) ℝ) (W : Matrix (Fin r) (Fin n) ℝ)
    (hproj : R * R.transpose + W * W.transpose =
      Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (x y : Fin r → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => g i = a), x i * y i) =
      ((R.transpose *ᵥ x) ⬝ᵥ (R.transpose *ᵥ y)) +
      ((W.transpose *ᵥ x) ⬝ᵥ (W.transpose *ᵥ y)) := by
  have he := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => x ⬝ᵥ (M *ᵥ y)) hproj
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add] at he
  rw [Matrix.dotProduct_mulVec _ R _, Matrix.dotProduct_mulVec _ W _,
    ← Matrix.mulVec_transpose R _, ← Matrix.mulVec_transpose W _] at he
  simpa only [Matrix.mulVec_diagonal,
    dotProduct, Finset.sum_filter, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
    zero_mul] using he.symm

lemma cavity_normalized_group_pairing_bound {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) (a : Fin m)
    (x y : EuclideanSpace ℝ (Fin r)) :
    |((cavityNormalizeFrame (X a)).transpose *ᵥ x.ofLp) ⬝ᵥ
      ((cavityNormalizeFrame (X a)).transpose *ᵥ y.ofLp)| ≤
      (‖(WithLp.toLp 2 ((cavityEigenspaceFrame X).transpose *ᵥ x.ofLp) :
          EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 +
        ‖(WithLp.toLp 2 ((cavityEigenspaceFrame X).transpose *ᵥ y.ofLp) :
          EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2) / 2 := by
  have hx : ‖(WithLp.toLp 2 ((cavityNormalizeFrame (X a)).transpose *ᵥ x.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
      ‖(WithLp.toLp 2 ((cavityEigenspaceFrame X).transpose *ᵥ x.ofLp) :
        EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 := by
    rw [cavity_eigenspace_projection_norm]
    exact Finset.single_le_sum (f := fun b =>
      ‖(WithLp.toLp 2 ((cavityNormalizeFrame (X b)).transpose *ᵥ x.ofLp) :
        EuclideanSpace ℝ (Fin n))‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have hy : ‖(WithLp.toLp 2 ((cavityNormalizeFrame (X a)).transpose *ᵥ y.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
      ‖(WithLp.toLp 2 ((cavityEigenspaceFrame X).transpose *ᵥ y.ofLp) :
        EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 := by
    rw [cavity_eigenspace_projection_norm]
    exact Finset.single_le_sum (f := fun b =>
      ‖(WithLp.toLp 2 ((cavityNormalizeFrame (X b)).transpose *ᵥ y.ofLp) :
        EuclideanSpace ℝ (Fin n))‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have h := cavity_masked_pairing_bound Finset.univ
    (WithLp.toLp 2 ((cavityNormalizeFrame (X a)).transpose *ᵥ x.ofLp))
    (WithLp.toLp 2 ((cavityNormalizeFrame (X a)).transpose *ᵥ y.ofLp))
  change |((cavityNormalizeFrame (X a)).transpose *ᵥ x.ofLp) ⬝ᵥ
    ((cavityNormalizeFrame (X a)).transpose *ᵥ y.ofLp)| ≤ _ at h
  exact h.trans (by linarith)

theorem cavity_retained_overlap_error {N n m d k : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (a : Fin m)
    (e : Fin (m * n) ≃ Fin (d + n)) (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (R : Matrix (Fin (N + n)) (Fin k) ℝ)
    (hproj : R * R.transpose +
      cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a) *
        (cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (J : Finset (Fin d)) (σ τ : Spin (N + n))
    (hbase : |(((R.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
      (R.transpose *ᵥ (specialRotation U (spinVector τ)).ofLp)) +
      ∑ j ∈ J, cavityFullSpecialCoordinates g B U σ j *
        cavityFullSpecialCoordinates g B U τ j) / N| ≤ 1) :
    |projectedOverlap (specialRotation U) (cavitySpectralGroup g a) σ τ -
      (((R.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
        (R.transpose *ᵥ (specialRotation U (spinVector τ)).ofLp)) +
        ∑ j ∈ J, cavityFullSpecialCoordinates g B U σ j *
          cavityFullSpecialCoordinates g B U τ j) / N| ≤
      ((2 * (n : ℝ) + 1) / N) *
        (1 + ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 +
          ‖cavityFullSpecialCoordinates g B U τ‖ ^ 2) := by
  let yσ := cavityFullSpecialCoordinates g B U σ
  let yτ := cavityFullSpecialCoordinates g B U τ
  let retained := (R.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
    (R.transpose *ᵥ (specialRotation U (spinVector τ)).ofLp)
  let fullSmall := ((cavityNormalizeFrame (cavitySpectralImage g
      (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose *ᵥ
        (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
    ((cavityNormalizeFrame (cavitySpectralImage g
      (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose *ᵥ
        (specialRotation U (spinVector τ)).ofLp)
  let baseSmall := ∑ j ∈ J, yσ j * yτ j
  have hf : |fullSmall| ≤ (‖yσ‖ ^ 2 + ‖yτ‖ ^ 2) / 2 + n := by
    have h := cavity_normalized_group_pairing_bound
      (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) a
      (specialRotation U (spinVector σ)) (specialRotation U (spinVector τ))
    rw [cavity_full_special_pythagoras g e U B hB hBT hA σ,
      cavity_full_special_pythagoras g e U B hB hBT hA τ] at h
    dsimp only [fullSmall, yσ, yτ]
    exact h.trans_eq (by ring)
  have hb : |baseSmall| ≤ (‖yσ‖ ^ 2 + ‖yτ‖ ^ 2) / 2 :=
    cavity_masked_pairing_bound J yσ yτ
  have hsmall : |fullSmall - baseSmall| ≤ ‖yσ‖ ^ 2 + ‖yτ‖ ^ 2 + n := by
    have h := (abs_sub _ _).trans (add_le_add hf hb)
    linarith
  have herr := cavity_normalized_overlap_error (n := n) hN retained fullSmall baseSmall
    (‖yσ‖ ^ 2 + ‖yτ‖ ^ 2 + n) (by positivity) hsmall hbase
  have he : projectedOverlap (specialRotation U) (cavitySpectralGroup g a) σ τ =
      (retained + fullSmall) / (N + n : ℕ) := by
    rw [projectedOverlap, cavitySpectralGroup,
      cavity_spectral_pairing_decomposition g a R _ hproj]
    exact (div_eq_inv_mul _ _).symm
  rw [he]
  apply herr.trans
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hN).le
  nlinarith [sq_nonneg ‖yσ‖, sq_nonneg ‖yτ‖,
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg ‖yσ‖),
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg ‖yτ‖)]

end InvariantIsing

end

end OAI
