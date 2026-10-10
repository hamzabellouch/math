import OAI.Analysis.KadisonKastler.MatrixAveraging
import OAI.Analysis.KadisonKastler.BlockMatrices
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-! # The amplified commutator estimate for finite matrix lifts -/

namespace KadisonKastler

noncomputable section

variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

/-- The constant diagonal amplification of an element. -/
def diagonalAmplification (a : A) : CStarMatrix n n A :=
  diagonalStarAlgHom n (fun _ => a)

@[simp]
theorem diagonalAmplification_sub (a b : A) :
    diagonalAmplification (n := n) (a - b) =
      diagonalAmplification (n := n) a - diagonalAmplification (n := n) b := by
  exact map_sub (diagonalStarAlgHom n) (fun _ => a) (fun _ => b)

/-- An element commuting with every matrix entry commutes with that matrix
when amplified on the diagonal. -/
theorem diagonalAmplification_commute (a : A) (s : CStarMatrix n n A)
    (hs : ∀ i j, Commute a (s i j)) : Commute (diagonalAmplification a) s := by
  apply CStarMatrix.ext
  intro i j
  change (Matrix.diagonal (fun _ : n => a) * CStarMatrix.ofMatrix.symm s) i j =
    (CStarMatrix.ofMatrix.symm s * Matrix.diagonal (fun _ : n => a)) i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (hs i j).eq

variable [PartialOrder A] [StarOrderedRing A]

theorem norm_diagonalAmplification_le (a : A) :
    ‖diagonalAmplification (n := n) a‖ ≤ ‖a‖ := by
  rw [diagonalAmplification, norm_diagonalStarAlgHom]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr (fun _ => le_rfl)

/-- A nearby element commuting with all entries of a unitary matrix controls
the amplified commutator, independently of the matrix size. -/
theorem norm_amplified_commutator_le (a b : A) (s : unitary (CStarMatrix n n A))
    {δ : ℝ} (hab : ‖a - b‖ ≤ δ) (hs : ∀ i j, Commute b ((s : CStarMatrix n n A) i j)) :
    ‖diagonalAmplification a * (s : CStarMatrix n n A) -
      (s : CStarMatrix n n A) * diagonalAmplification a‖ ≤ 2 * δ := by
  have hc := (diagonalAmplification_commute b (s : CStarMatrix n n A) hs).eq
  have he : diagonalAmplification a * (s : CStarMatrix n n A) -
      (s : CStarMatrix n n A) * diagonalAmplification a =
      diagonalAmplification (a - b) * (s : CStarMatrix n n A) -
        (s : CStarMatrix n n A) * diagonalAmplification (a - b) := by
    rw [diagonalAmplification_sub, sub_mul, mul_sub, hc]
    abel
  rw [he]
  calc
    _ ≤ ‖diagonalAmplification (n := n) (a - b) * (s : CStarMatrix n n A)‖ +
        ‖(s : CStarMatrix n n A) * diagonalAmplification (a - b)‖ := norm_sub_le _ _
    _ = 2 * ‖diagonalAmplification (n := n) (a - b)‖ := by
      rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
      ring
    _ ≤ 2 * δ := mul_le_mul_of_nonneg_left ((norm_diagonalAmplification_le _).trans hab)
      (by norm_num)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance scalarAmplificationOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance scalarAmplificationStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The controlled-representative estimate in the free-lift construction:
a unitary matrix over a finite matrix subalgebra has commutator at most
`2δ`, where `δ` controls the scalar derivation on the ambient algebra. -/
theorem matrixUnit_lift_commutator_le (M : VonNeumannAlgebra H)
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (hE : E.algebra ≤ M.toStarSubalgebra)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (s : unitary (CStarMatrix n n (H →L[ℂ] H)))
    (hs : ∀ i j, (s : CStarMatrix n n (H →L[ℂ] H)) i j ∈ E.algebra) :
    ‖diagonalAmplification h * (s : CStarMatrix n n (H →L[ℂ] H)) -
      (s : CStarMatrix n n (H →L[ℂ] H)) * diagonalAmplification h‖ ≤ 2 * δ := by
  obtain ⟨h0, hc, hd, _, _⟩ := exists_matrixUnitAverage M E hE h hδ hb
  exact norm_amplified_commutator_le h h0 s hd (fun i j => (hc _ (hs i j)).symm)

end

end KadisonKastler

end OAI
