import OAI.Probability.InvariantIsing.Cavity.CavityOrientation
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledProjectors

namespace OAI

/-! The SO orientation correction preserves the full physical labeled
projector/frame data, as well as the compression matrices. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityOrientationSign_gram {N : ℕ} (hN : 0 < N) (U : Orthogonal N) :
    (cavityOrientationSign hN U).transpose * cavityOrientationSign hN U = 1 := by
  simpa only [cavityOrientationSign, Matrix.diagonal_transpose] using
    cavityOrientationSign_square hN U

lemma cavityOrientationSign_diagonal {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (lam : Fin N → ℝ) :
    cavityOrientationSign hN U * Matrix.diagonal lam * (cavityOrientationSign hN U).transpose =
      Matrix.diagonal lam := by
  have hc : cavityOrientationSign hN U * Matrix.diagonal lam =
      Matrix.diagonal lam * cavityOrientationSign hN U := by
    simp only [cavityOrientationSign, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [hc, Matrix.mul_assoc, cavityOrientationSign_square, Matrix.mul_one]

lemma cavityOrientationLift_eigenspace {N n m : ℕ} (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m) (U : Orthogonal (N+n)) :
    cavityEigenspaceFrame (cavitySpectralImage g
      (cavityColumns (cavitySpecialOrthogonal (cavityOrientationLift hN U)))) =
    cavityOrientationSign hN U * cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U)) := by
  have hx : cavitySpectralImage g
      (cavityColumns (cavitySpecialOrthogonal (cavityOrientationLift hN U))) =
      fun a => cavityOrientationSign hN U * cavitySpectralImage g (cavityColumns U) a := by
    funext a
    ext i j
    simp only [cavitySpectralImage, cavityColumns, cavitySpecialOrthogonal,
      cavityOrientationLift, cavityOrientationSign, Matrix.diagonal_mul]
    split_ifs <;> ring
  rw [hx, cavityEigenspaceFrame_left_orthogonal _ _ (cavityOrientationSign_gram hN U)]

lemma cavityOrientationLift_physicalBase {N n m d : ℕ} (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m) (U : Orthogonal (N+n)) (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    cavityPhysicalBase g lam B A₀ (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityPhysicalBase g lam B A₀ U := by
  let D := cavityOrientationSign hN U
  let O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ := U
  let W := cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U))
  let J := Matrix.diagonal (fun i => lam (g i))
  have hD : D.transpose * D = 1 := cavityOrientationSign_gram hN U
  have hj : D * J * D.transpose = J := cavityOrientationSign_diagonal hN U _
  have hr := cavityBaseReplacement_conjugate J D W (cavityRepeatedSpectrum (n := n) lam)
    (B (cavityCompressionGrams g U)) A₀
  rw [hj] at hr
  unfold cavityPhysicalBase
  rw [cavityOrientationLift_compression, cavityOrientationLift_eigenspace]
  change ((D*O).transpose * cavityBaseReplacement J (D*W)
    (cavityRepeatedSpectrum (n := n) lam) (B (cavityCompressionGrams g U)) A₀ * (D*O)).submatrix
      (Fin.castAdd n) (Fin.castAdd n) = _
  rw [hr, Matrix.transpose_mul]
  have he (R : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) :
      (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * D.transpose *
        (D*R*D.transpose) * (D*(U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)) =
      (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * R *
        (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) := by
    calc
      _ = (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * (D.transpose*D) * R *
          (D.transpose*D) * (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hD]; simp
  rw [he]

lemma cavityOrientationLift_physicalSpecial {N n m d : ℕ} (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m) (U : Orthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ) :
    cavityPhysicalSpecial g B (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityPhysicalSpecial g B U := by
  unfold cavityPhysicalSpecial
  rw [cavityOrientationLift_compression, cavityOrientationLift_eigenspace]
  change cavityReservoirRows (((cavityOrientationSign hN U *
    (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)).transpose) *
      ((cavityOrientationSign hN U * _) * _)) = _
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (cavityOrientationSign hN U).transpose
    (cavityOrientationSign hN U), cavityOrientationSign_gram, Matrix.one_mul]

lemma cavityOrientationLift_projectors {N n m d : ℕ} (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m) (U : Orthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) :
    cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityPhysicalLabeledProjectors g B a₀ U := by
  refine Prod.ext ?_ (cavityOrientationLift_physicalSpecial hN g U B)
  funext a
  exact cavityOrientationLift_physicalBase (N := N) (n := n) (m := m) (d := d)
    hN g U (fun b => if b=a then 1 else 0) B
    (Matrix.diagonal (fun j => if a₀ j=a then 1 else 0))

end InvariantIsing

end

end OAI
