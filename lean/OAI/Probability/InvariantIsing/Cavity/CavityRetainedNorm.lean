import OAI.Probability.InvariantIsing.Cavity.CavityRetainedPairing

namespace OAI

/-! The retained and special base coordinates have total squared norm
equal to the number of reservoir spins. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_retained_stack_norm {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (z : EuclideanSpace ℝ (Fin r)) :
    ‖(WithLp.toLp 2 ((cavityRetainedStack k R).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ ((a : Fin m) × Fin (k a)))‖ ^ 2 =
      ∑ a, ‖(WithLp.toLp 2 ((R a).transpose *ᵥ z.ofLp) :
        EuclideanSpace ℝ (Fin (k a)))‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Matrix.mulVec,
    Matrix.transpose_apply, cavityRetainedStack, Fintype.sum_sigma]

theorem cavity_retained_special_norm {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a) *
        (cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (σ : Spin (N + n)) :
    (∑ a, ‖(WithLp.toLp 2 ((R a).transpose *ᵥ
      (specialRotation U (spinVector σ)).ofLp) : EuclideanSpace ℝ (Fin (k a)))‖ ^ 2) +
      ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 = N := by
  have h := cavity_projection_norm_split (cavityRetainedStack k R)
    (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))))
    (cavityRetainedStack_complete g (cavityColumns (cavitySpecialOrthogonal U)) k R hproj)
    (specialRotation U (spinVector σ))
  rw [(specialRotation U).norm_map, spinVector_norm_sq, cavity_retained_stack_norm,
    cavity_full_special_pythagoras g e U B hB hBT hA σ] at h
  push_cast at h
  linarith

theorem cavity_retained_base_overlap_bound {N n m d : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a) *
        (cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (a : Fin m) (J : Finset (Fin d)) (σ τ : Spin (N + n)) :
    |(((R a).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
      ((R a).transpose *ᵥ (specialRotation U (spinVector τ)).ofLp) +
      ∑ j ∈ J, cavityFullSpecialCoordinates g B U σ j *
        cavityFullSpecialCoordinates g B U τ j) / N| ≤ 1 := by
  let r := fun σ : Spin (N + n) => (WithLp.toLp 2
    ((R a).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) :
      EuclideanSpace ℝ (Fin (k a)))
  let y := fun σ => cavityFullSpecialCoordinates g B U σ
  have hn (σ : Spin (N + n)) : ‖r σ‖ ^ 2 + ‖y σ‖ ^ 2 ≤ N := by
    have ht := cavity_retained_special_norm g e U B hB hBT hA k R hproj σ
    have hs : ‖r σ‖ ^ 2 ≤ ∑ b, ‖(WithLp.toLp 2 ((R b).transpose *ᵥ
        (specialRotation U (spinVector σ)).ofLp) : EuclideanSpace ℝ (Fin (k b)))‖ ^ 2 :=
      Finset.single_le_sum (f := fun b => ‖(WithLp.toLp 2 ((R b).transpose *ᵥ
        (specialRotation U (spinVector σ)).ofLp) : EuclideanSpace ℝ (Fin (k b)))‖ ^ 2)
        (fun b _ => sq_nonneg _) (Finset.mem_univ a)
    dsimp only [y]
    linarith
  have hr := cavity_masked_pairing_bound Finset.univ (r σ) (r τ)
  have hy := cavity_masked_pairing_bound J (y σ) (y τ)
  have hp : |(r σ).ofLp ⬝ᵥ (r τ).ofLp + ∑ j ∈ J, y σ j * y τ j| ≤ N := by
    change |(∑ i, r σ i * r τ i) + ∑ j ∈ J, y σ j * y τ j| ≤ N
    have hh := (abs_add_le _ _).trans (add_le_add hr hy)
    linarith [hn σ, hn τ]
  rw [abs_div, abs_of_pos (show (0 : ℝ) < (N : ℝ) from Nat.cast_pos.mpr hN)]
  exact (div_le_one (Nat.cast_pos.mpr hN)).mpr hp

def cavityRetainedBaseOverlap {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (U : SpecialOrthogonal (N + n)) (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (J : Fin m → Finset (Fin d)) (a : Fin m) (σ τ : Spin (N + n)) : ℝ :=
  (((R a).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
    ((R a).transpose *ᵥ (specialRotation U (spinVector τ)).ofLp) +
      ∑ j ∈ J a, cavityFullSpecialCoordinates g B U σ j *
        cavityFullSpecialCoordinates g B U τ j) / N

theorem cavity_retained_base_comparison {N n m d : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a) *
        (cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (J : Fin m → Finset (Fin d)) (a : Fin m) (σ τ : Spin (N + n)) :
    |projectedOverlap (specialRotation U) (cavitySpectralGroup g a) σ τ -
      cavityRetainedBaseOverlap g U B k R J a σ τ| ≤
      ((2 * (n : ℝ) + 1) / N) *
        (1 + ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 +
          ‖cavityFullSpecialCoordinates g B U τ‖ ^ 2) := by
  exact cavity_retained_overlap_error hN g a e U B hB hBT hA (R a) (hproj a) (J a) σ τ
    (cavity_retained_base_overlap_bound hN g e U B hB hBT hA k R hproj a (J a) σ τ)

end InvariantIsing

end

end OAI
