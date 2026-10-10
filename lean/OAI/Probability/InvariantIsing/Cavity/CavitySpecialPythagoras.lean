import OAI.Probability.InvariantIsing.Cavity.CavityProjectionGeometry
import OAI.Probability.InvariantIsing.Cavity.CavityConcreteComplement

namespace OAI

/-! The special coordinates and the physical cavity spins exhaust the
normalized spectral-image coordinates. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_complement_projection_reindex {s d n : ℕ}
    (e : Fin s ≃ Fin (d + n))
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hT : T.transpose * T = 1)
    (hBT : B.transpose * T = 0) :
    B * B.transpose + T * T.transpose = 1 := by
  have hTB : T.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBT
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : (Matrix.fromCols B T).transpose * Matrix.fromCols B T = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hB, hBT, hTB, hT,
      Matrix.fromBlocks_one]
  have h := (Matrix.mul_eq_one_comm_of_equiv
    ((finSumFinEquiv : Fin d ⊕ Fin n ≃ Fin (d + n)).trans e.symm)).mp hQ
  simpa only [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using h

lemma cavity_projection_norm_split {s n : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin s) ι ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hcomplete : B * B.transpose + T * T.transpose = 1)
    (z : EuclideanSpace ℝ (Fin s)) :
    ‖z‖ ^ 2 =
      ‖(WithLp.toLp 2 (B.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ ι)‖ ^ 2 +
      ‖(WithLp.toLp 2 (T.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  have he : z.ofLp ⬝ᵥ ((B * B.transpose + T * T.transpose) *ᵥ z.ofLp) =
      z.ofLp ⬝ᵥ z.ofLp := by rw [hcomplete, Matrix.one_mulVec]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add] at he
  rw [Matrix.dotProduct_mulVec _ B _, Matrix.dotProduct_mulVec _ T _,
    ← Matrix.mulVec_transpose B _, ← Matrix.mulVec_transpose T _] at he
  simpa only [dotProduct, pow_two, PiLp.toLp_apply] using he.symm

lemma cavityColumns_transpose_rotation {N n : ℕ} (U : SpecialOrthogonal (N + n))
    (x : EuclideanSpace ℝ (Fin (N + n))) :
    (cavityColumns (cavitySpecialOrthogonal U)).transpose *ᵥ
      (specialRotation U x).ofLp = fun j => x (Fin.natAdd N j) := by
  have hU : (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
      (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' _ _).mp (cavitySpecialOrthogonal U).property
  have hx : (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *ᵥ
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *ᵥ x.ofLp) = x.ofLp := by
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  funext j
  exact congrFun hx (Fin.natAdd N j)

theorem cavity_full_special_pythagoras {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (σ : Spin (N + n)) :
    ‖(WithLp.toLp 2 ((cavityEigenspaceFrame
      (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)))).transpose *ᵥ
        (specialRotation U (spinVector σ)).ofLp) : EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 =
      ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 + n := by
  let W := cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)))
  let T := cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U))
  have hT : T.transpose * T = 1 := by
    have h := cavitySpectralStack_gram (cavityCompressionGrams g (cavitySpecialOrthogonal U))
      (fun a => (hA a).posSemidef)
    exact h.trans (cavityCompressionGrams_sum g (cavitySpecialOrthogonal U))
  have hWT : W * T = cavityColumns (cavitySpecialOrthogonal U) := by
    exact (cavityEigenspaceFrame_stack _ hA).trans (cavitySpectralImage_sum g _)
  have htcoord : T.transpose *ᵥ (W.transpose *ᵥ
      (specialRotation U (spinVector σ)).ofLp) =
      fun j => spinValue (σ (Fin.natAdd N j)) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hWT]
    exact cavityColumns_transpose_rotation U (spinVector σ)
  have h := cavity_projection_norm_split B T
    (cavity_complement_projection_reindex e B T hB hT hBT)
    (WithLp.toLp 2 (W.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp))
  have hy : (WithLp.toLp 2 (B.transpose *ᵥ
      (W.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp)) : EuclideanSpace ℝ (Fin d)) =
      cavityFullSpecialCoordinates g B U σ := by
    simp only [cavityFullSpecialCoordinates, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, W]
  have hn : ‖(WithLp.toLp 2 (T.transpose *ᵥ
      (W.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = n := by
    rw [htcoord, EuclideanSpace.real_norm_sq_eq]
    simp only [spinValue_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact h.trans (congrArg₂ (· + ·) (congrArg (fun z => ‖z‖ ^ 2) hy) hn)

end InvariantIsing

end

end OAI
