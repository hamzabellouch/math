import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.Spin

namespace OAI

/-!
# Exact singlet mediator calculations

The positive-spin conversion uses the singlet mediator of Piddock–Montanaro,
*The complexity of antiferromagnetic interactions and 2D lattices*, Quantum
Information and Computation 17 (2017), Section 2.4 and Lemma 5.
The Pauli contractions and penalty identities use an unnormalized singlet
vector, whose expectation values are twice the normalized values.
-/

noncomputable section

namespace ContinuumCoulomb

open Matrix
open scoped BigOperators

def pauli (μ : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![pauliX, pauliY, pauliZ] μ

def firstPauli (μ : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  twoSpinTensor (pauli μ) 1

def secondPauli (μ : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  twoSpinTensor 1 (pauli μ)

/-- Matrix element in the singlet of squared norm two. -/
def singletMatrixElement (A : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ i, star (spinSinglet i) * (A *ᵥ spinSinglet) i

theorem singlet_first_pauli (μ : Fin 3) :
    singletMatrixElement (firstPauli μ) = 0 := by
  fin_cases μ <;>
    norm_num [singletMatrixElement, firstPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem singlet_second_pauli (μ : Fin 3) :
    singletMatrixElement (secondPauli μ) = 0 := by
  fin_cases μ <;>
    norm_num [singletMatrixElement, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

/-- Same-member singlet contraction: normalized value `δμν`. -/
theorem singlet_first_first (μ ν : Fin 3) :
    singletMatrixElement (firstPauli μ * firstPauli ν) =
      if μ = ν then 2 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [singletMatrixElement, firstPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

/-- Same-member singlet contraction on the other mediator. -/
theorem singlet_second_second (μ ν : Fin 3) :
    singletMatrixElement (secondPauli μ * secondPauli ν) =
      if μ = ν then 2 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [singletMatrixElement, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

/-- Opposite-member singlet contraction: normalized value `-δμν`. -/
theorem singlet_first_second (μ ν : Fin 3) :
    singletMatrixElement (firstPauli μ * secondPauli ν) =
      if μ = ν then -2 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [singletMatrixElement, firstPauli, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem singlet_second_first (μ ν : Fin 3) :
    singletMatrixElement (secondPauli μ * firstPauli ν) =
      if μ = ν then -2 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [singletMatrixElement, firstPauli, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

/-- Orthogonal projection onto the one-dimensional singlet space. -/
def singletProjector : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 1 / 2, -(1 / 2), 0;
     0, -(1 / 2), 1 / 2, 0;
     0, 0, 0, 0]

theorem singletProjector_idempotent :
    singletProjector * singletProjector = singletProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singletProjector, Matrix.mul_apply, Fin.sum_univ_succ]

theorem singletProjector_singlet :
    singletProjector *ᵥ spinSinglet = spinSinglet := by
  ext i
  fin_cases i <;>
    norm_num [singletProjector, spinSinglet, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The mediator excitation penalty is exactly four times the triplet projection. -/
theorem singlet_penalty_eq :
    heisenberg + (3 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
      (4 : ℂ) • (1 - singletProjector) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, singletProjector, Matrix.one_apply]

/-- Each Pauli action takes the singlet orthogonally to its kernel space. -/
theorem singletProjector_first_pauli (μ : Fin 3) :
    singletProjector *ᵥ (firstPauli μ *ᵥ spinSinglet) = 0 := by
  fin_cases μ <;>
    ext i <;> fin_cases i <;>
    norm_num [singletProjector, firstPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem singletProjector_second_pauli (μ : Fin 3) :
    singletProjector *ᵥ (secondPauli μ *ᵥ spinSinglet) = 0 := by
  fin_cases μ <;>
    ext i <;> fin_cases i <;>
    norm_num [singletProjector, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem firstPauli_sq (μ : Fin 3) : firstPauli μ * firstPauli μ = 1 := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [firstPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem secondPauli_sq (μ : Fin 3) : secondPauli μ * secondPauli μ = 1 := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [secondPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem first_second_pauli (μ : Fin 3) :
    firstPauli μ * secondPauli μ = twoSpinTensor (pauli μ) (pauli μ) := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [firstPauli, secondPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem second_first_pauli (μ : Fin 3) :
    secondPauli μ * firstPauli μ = twoSpinTensor (pauli μ) (pauli μ) := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [firstPauli, secondPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem sum_first_second_pauli :
    (∑ μ : Fin 3, firstPauli μ * secondPauli μ) = heisenberg := by
  simp_rw [first_second_pauli]
  rw [heisenberg_eq_pauli]
  simp [pauli, Fin.sum_univ_succ, add_assoc]

theorem sum_second_first_pauli :
    (∑ μ : Fin 3, secondPauli μ * firstPauli μ) = heisenberg := by
  simp_rw [second_first_pauli]
  rw [heisenberg_eq_pauli]
  simp [pauli, Fin.sum_univ_succ, add_assoc]

/-- The second mediator spoke can meet the same or the opposite member. -/
def otherMediatorPauli (opposite : Bool) (μ : Fin 3) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  if opposite then secondPauli μ else firstPauli μ

/-- Compression of the square of the two-spoke coupling to the normalized
mediator singlet.  The first matrix factors act on the external pair;
the matrix elements contract the mediator pair. -/
def mediatorContraction (opposite : Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • ∑ μ : Fin 3, ∑ ν : Fin 3,
    (singletMatrixElement (firstPauli μ * firstPauli ν) •
        (firstPauli μ * firstPauli ν) +
      singletMatrixElement (firstPauli μ * otherMediatorPauli opposite ν) •
        (firstPauli μ * secondPauli ν) +
      singletMatrixElement (otherMediatorPauli opposite μ * firstPauli ν) •
        (secondPauli μ * firstPauli ν) +
      singletMatrixElement
          (otherMediatorPauli opposite μ * otherMediatorPauli opposite ν) •
        (secondPauli μ * secondPauli ν))

theorem mediatorContraction_same :
    mediatorContraction false =
      (6 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) + (2 : ℂ) • heisenberg := by
  simp only [mediatorContraction, otherMediatorPauli, Bool.false_eq_true, ↓reduceIte,
    singlet_first_first, Finset.sum_add_distrib]
  simp [ite_smul, Finset.smul_sum, smul_add, smul_smul]
  simp_rw [firstPauli_sq, secondPauli_sq]
  rw [sum_first_second_pauli, sum_second_first_pauli]
  ext i j
  simp
  by_cases h : i = j
  · simp [Matrix.ofNat_apply, Matrix.one_apply, h]
    ring
  · simp [Matrix.ofNat_apply, h]
    ring

theorem mediatorContraction_opposite :
    mediatorContraction true =
      (6 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - (2 : ℂ) • heisenberg := by
  simp only [mediatorContraction, otherMediatorPauli, ↓reduceIte,
    singlet_first_first, singlet_first_second, singlet_second_first, singlet_second_second,
    Finset.sum_add_distrib]
  simp [ite_smul, Finset.smul_sum, smul_add, smul_smul]
  simp_rw [firstPauli_sq, secondPauli_sq]
  rw [sum_first_second_pauli, sum_second_first_pauli]
  ext i j
  simp
  by_cases h : i = j
  · simp [Matrix.ofNat_apply, Matrix.one_apply, h]
    ring
  · simp [Matrix.ofNat_apply, h]
    ring

/-- The inverse of the unit mediator penalty is `1/4` on the excited
space, and every spoke takes the singlet there.  The contraction hence
has the negative second-order prefactor `-v²/4`. -/
def mediatorSecondOrder (opposite : Bool) (v : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-(v ^ 2 / 4 : ℝ) : ℂ) • mediatorContraction opposite

theorem mediatorSecondOrder_same (v : ℝ) :
    mediatorSecondOrder false v =
      (-(v ^ 2 / 2 : ℝ) : ℂ) • heisenberg -
        ((3 * v ^ 2 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [mediatorSecondOrder, mediatorContraction_same]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem mediatorSecondOrder_opposite (v : ℝ) :
    mediatorSecondOrder true v =
      ((v ^ 2 / 2 : ℝ) : ℂ) • heisenberg -
        ((3 * v ^ 2 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [mediatorSecondOrder, mediatorContraction_opposite]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

end ContinuumCoulomb

end

end OAI
