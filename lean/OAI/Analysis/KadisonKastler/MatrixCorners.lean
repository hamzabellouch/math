import OAI.Analysis.KadisonKastler.MatrixTrace

namespace OAI

/-! # Splitting projections in a coordinate matrix corner -/

namespace KadisonKastler

noncomputable section

variable {B ι : Type*} [CStarAlgebra B] [Fintype ι] [DecidableEq ι]

def matrixCorner (i : ι) (b : B) : CStarMatrix ι ι B :=
  CStarMatrix.ofMatrix (Matrix.single i i b)

omit [Fintype ι] in
theorem matrixCorner_injective (i : ι) : Function.Injective (matrixCorner (B := B) i) := by
  intro a b h
  simpa [matrixCorner, Matrix.single] using congrArg (fun x : CStarMatrix ι ι B => x i i) h

omit [Fintype ι] in
@[simp]
theorem matrixCorner_zero (i : ι) : matrixCorner (B := B) i 0 = 0 := by
  ext j k
  simp [matrixCorner, Matrix.single]

theorem matrixCorner_mul (i : ι) (a b : B) :
    matrixCorner i (a * b) = matrixCorner i a * matrixCorner i b := by
  exact (Matrix.single_mul_single_same a i i i b).symm

omit [Fintype ι] in
theorem matrixCorner_star (i : ι) (b : B) :
    matrixCorner i (star b) = star (matrixCorner i b) := by
  change Matrix.single i i (star b) = Matrix.conjTranspose (Matrix.single i i b)
  exact (Matrix.conjTranspose_single i i b).symm

theorem matrixCorner_isStarProjection_iff (i : ι) (b : B) :
    IsStarProjection (matrixCorner i b) ↔ IsStarProjection b := by
  constructor
  · intro h
    constructor
    · apply matrixCorner_injective i
      rw [matrixCorner_mul, h.isIdempotentElem.eq]
    · apply matrixCorner_injective i
      rw [matrixCorner_star, h.isSelfAdjoint.star_eq]
  · intro h
    constructor
    · change matrixCorner i b * matrixCorner i b = matrixCorner i b
      rw [← matrixCorner_mul, h.isIdempotentElem.eq]
    · change star (matrixCorner i b) = matrixCorner i b
      rw [← matrixCorner_star, h.isSelfAdjoint.star_eq]

theorem matrixCorner_reconstruct (i : ι) (x : CStarMatrix ι ι B)
    (hleft : matrixCorner i 1 * x = x) (hright : x * matrixCorner i 1 = x) :
    x = matrixCorner i (x i i) := by
  calc
    x = matrixCorner i 1 * x * matrixCorner i 1 := by rw [hleft, hright]
    _ = matrixCorner i (x i i) := by
      apply CStarMatrix.ofMatrix.symm.injective
      change Matrix.single i i (1 : B) * CStarMatrix.ofMatrix.symm x *
        Matrix.single i i (1 : B) = Matrix.single i i (x i i)
      simpa only [one_mul, mul_one, CStarMatrix.ofMatrix_symm_apply] using
        (Matrix.single_mul_mul_single i i i i (1 : B) (CStarMatrix.ofMatrix.symm x) 1)

/-- A diagonal corner inherits exactly the projection-splitting property
of the original algebra. -/
theorem matrixCorner_diffuse
    (hdiff : ∀ p : B, IsStarProjection p → p ≠ 0 →
      ∃ q : B, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (i : ι) (p : CStarMatrix ι ι B) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hleft : matrixCorner i 1 * p = p) (hright : p * matrixCorner i 1 = p) :
    ∃ q : CStarMatrix ι ι B, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
      p * q = q ∧ q * p = q := by
  have hrec := matrixCorner_reconstruct i p hleft hright
  have hpi : IsStarProjection (p i i) :=
    (matrixCorner_isStarProjection_iff i _).mp (hrec ▸ hp)
  have hpi0 : p i i ≠ 0 := by
    intro h
    rw [h, matrixCorner_zero] at hrec
    exact hp0 hrec
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hdiff (p i i) hpi hpi0
  refine ⟨matrixCorner i q, (matrixCorner_isStarProjection_iff i q).mpr hq, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hq0 (matrixCorner_injective i (h.trans (matrixCorner_zero i).symm))
  · intro h
    exact hqp (matrixCorner_injective i (h.trans hrec))
  · rw [hrec, ← matrixCorner_mul, hpq]
  · rw [hrec, ← matrixCorner_mul, hqp']

end

end KadisonKastler

end OAI
