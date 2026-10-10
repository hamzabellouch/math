import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyCorrectness

namespace OAI

/-! Polynomial raw four-spin compiler with its full-space spectral guarantee. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open Matrix
open scoped BigOperators Classical

theorem pack_weight {n : ℕ} (t : QMAXZTerm n) (J : ℚ) : (pack t J).2.2.2 = J := by
  cases t <;> rfl

theorem mass_packed {n m : ℕ} (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    mass (packed t J) = ∑ e, |J e| := by
  simp only [mass,packed,List.map_ofFn,List.sum_ofFn,Function.comp_apply,pack_weight]

theorem size_packed {n m : ℕ} (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    size (packed t J) = rationalInputSize J := by
  simp only [size,packed,List.length_ofFn]
  rw [← packed,mass_packed]
  simp only [rationalInputSize,Fintype.card_fin]

theorem budget_packed {n m : ℕ} (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    budget (packed t J) = rationalBudget J := by
  simp only [budget,size_packed,rationalBudget]

theorem scale_packed {n m : ℕ} (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    scale N (packed t J) = rationalPenalty N J := by
  simp only [scale,budget_packed,rationalPenalty]

theorem bits_packed {n m : ℕ} (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    bits (n,N,packed t J) = boundedPrecision N t J := by
  change QuantumAxisSample.precision
    (universalErrorBudget n (packed t J).length (scale N (packed t J)) (mass (packed t J))) N = _
  rw [scale_packed,mass_packed]
  simp only [packed,List.length_ofFn,boundedPrecision,Fintype.card_fin]

def rawBondMatrix (n : ℕ) (b : Bond) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  if hi : b.1 < n then if hj : b.2.1 < n then
    (b.2.2:ℂ) • sourceHeisenbergMatrix n ⟨b.1,hi⟩ ⟨b.2.1,hj⟩ else 0 else 0

def rawMatrix (n : ℕ) (out : List Bond × ℚ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  (out.1.map (rawBondMatrix n)).sum+out.2 • 1

theorem rawBondMatrix_erase {n : ℕ} (b : TypedBond n) :
    rawBondMatrix n (erase b) = typedBondMatrix b := by
  simp only [rawBondMatrix,erase,b.1.isLt,b.2.1.isLt,↓reduceDIte,typedBondMatrix]

theorem fullMatrix_packed {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    rawMatrix (n*4) (fullBonds (n,(k,r),packed t J),fullScalar (n,(k,r),packed t J)) =
      matrixValue k r t J := by
  rw [rawMatrix,fullBonds_packed,fullScalar_packed,List.map_map]
  simp only [Function.comp_def,rawBondMatrix_erase]
  rw [← family_matrix]
  rw [termScalar_sum]

theorem compile_matrix {n m : ℕ} (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    rawMatrix (n*4) (compile (n,N,packed t J)) = boundedMatrix N t J := by
  unfold compile scheduled
  rw [bits_packed,scale_packed,fullMatrix_packed]
  rfl

theorem compile_accuracy {n m : ℕ} (N : ℕ) (hN : 0 < N) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f) :
    |MediatorGraph.normalizedBottom (rawMatrix (n*4) (compile (n,N,packed t J)))-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 2/(N:ℝ) := by
  rw [compile_matrix]
  exact boundedMatrix_accuracy N hN t J hprivate

theorem compile_valid {n m : ℕ} (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (b : Bond) (hb : b ∈ (compile (n,N,packed t J)).1) :
    b.1 < n*4 ∧ b.2.1 < n*4 ∧ b.1 ≠ b.2.1 :=
  fullBonds_valid (bits (n,N,packed t J)) (scale N (packed t J)) t J b hb

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
