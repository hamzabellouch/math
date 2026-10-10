import OAI.Analysis.PureInfiniteness.ColumnReturnEstimates
import OAI.Analysis.JiangSu.Nonunital.MatrixDiagonal

namespace OAI

/-! The concrete return column and scalar sample matrices used by the joint
spectral compression. All formulas are identities in finite matrix algebras. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype J] [DecidableEq J]

def sqrtColumn (g : J → A) : CStarMatrix J (Fin 1) A :=
  CStarMatrix.ofMatrix (fun j _ => CFC.sqrt (g j))

def scalarSample (t : J → ℝ) : CStarMatrix J J A :=
  NonunitalGamma.diagonalHom (fun j => (t j : ℂ) • (1 : A))

omit [DecidableEq J] in
lemma sqrtColumn_gram (g : J → A) (hg : ∀ j, 0 ≤ g j) :
    (sqrtColumn g).conjTranspose * sqrtColumn g =
      CStarMatrix.toOneByOne (Fin 1) ℂ A (∑ j, g j) := by
  ext i k
  change (∑ j, star (CFC.sqrt (g j)) * CFC.sqrt (g j)) = ∑ j, g j
  apply Finset.sum_congr rfl
  intro j _
  rw [(CFC.sqrt_nonneg (g j)).star_eq, CFC.sqrt_mul_sqrt_self (g j) (hg j)]

omit [DecidableEq J] in
lemma sqrtColumn_norm_le_one (g : J → A) (hg : ∀ j, 0 ≤ g j) (hs : ‖∑ j, g j‖ ≤ 1) :
    ‖sqrtColumn g‖ ≤ 1 := by
  have he : ‖sqrtColumn g‖ ^ 2 = ‖∑ j, g j‖ := by
    rw [← rectangular_norm_initial, sqrtColumn_gram g hg]
    exact NonUnitalStarAlgHom.norm_map
      (CStarMatrix.toOneByOne (Fin 1) ℂ A).toNonUnitalStarAlgHom
      (CStarMatrix.toOneByOne (Fin 1) ℂ A).injective _
  nlinarith [norm_nonneg (sqrtColumn g)]

lemma scalarSample_mul_sqrtColumn (t : J → ℝ) (g : J → A) (j : J) (k : Fin 1) :
    (scalarSample (A := A) t * sqrtColumn g) j k = (t j : ℂ) • CFC.sqrt (g j) := by
  change (∑ l, (if j = l then (t j : ℂ) • (1 : A) else 0) * CFC.sqrt (g l)) = _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    smul_mul_assoc, one_mul]

lemma columnReturn_scalarSample (t : J → ℝ) (g : J → A) (hg : ∀ j, 0 ≤ g j) :
    columnReturn (sqrtColumn g) (scalarSample t) =
      CStarMatrix.toOneByOne (Fin 1) ℂ A (∑ j, (t j : ℂ) • g j) := by
  unfold columnReturn
  rw [rectangular_mul_assoc]
  ext i k
  change (∑ j, star (CFC.sqrt (g j)) *
    (scalarSample (A := A) t * sqrtColumn g : CStarMatrix J (Fin 1) A) j k) = _
  simp only [scalarSample_mul_sqrtColumn]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, (CFC.sqrt_nonneg (g j)).star_eq,
    CFC.sqrt_mul_sqrt_self (g j) (hg j)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma scalarSample_square (t : J → ℝ) :
    scalarSample (A := A) t * scalarSample t = scalarSample (fun j => (t j) ^ 2) := by
  unfold scalarSample
  rw [← map_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, smul_mul_assoc, mul_smul_comm, one_mul, smul_smul,
    pow_two, Complex.ofReal_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma scalarSample_selfAdjoint (t : J → ℝ) :
    (scalarSample (A := A) t).conjTranspose = scalarSample t := by
  change star (scalarSample (A := A) t) = scalarSample t
  unfold scalarSample
  rw [← map_star]
  congr 1
  funext j
  simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma scalarSample_commute_diagonal (t : J → ℝ) (y : J → A) :
    scalarSample (A := A) t * NonunitalGamma.diagonalHom y =
      NonunitalGamma.diagonalHom y * scalarSample t := by
  unfold scalarSample
  rw [← map_mul, ← map_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
lemma diagonal_of_offdiagonal_zero (Y : CStarMatrix J J A)
    (hY : ∀ i j, i ≠ j → Y i j = 0) :
    Y = NonunitalGamma.diagonalHom (fun j => Y j j) := by
  ext i j
  change Y i j = if i = j then Y i i else 0
  split_ifs with hij
  · subst j
    rfl
  · exact hY i j hij

end WeakPureInfiniteness

end

end OAI
