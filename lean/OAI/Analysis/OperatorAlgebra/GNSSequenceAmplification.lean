import OAI.Analysis.Nuclearity.NuclearQuotientExpectation
import OAI.Analysis.ModularRecovery.TomitaFundamental

namespace OAI

/-! Countable diagonal amplification and its double commutant. This is the
concrete amplification used to produce a separating vector. -/
noncomputable section
open scoped InnerProductSpace
namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev SequenceHilbert (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

def sequenceDiagonal (T : H →L[ℂ] H) : SequenceHilbert H →L[ℂ] SequenceHilbert H :=
  lp.mapCLM 2 (fun _ => T) (norm_nonneg T) (fun _ => le_rfl)

omit [CompleteSpace H] in
lemma sequenceDiagonal_apply (T : H →L[ℂ] H) (x : SequenceHilbert H) (n : ℕ) :
    sequenceDiagonal T x n = T (x n) := rfl

lemma sequenceDiagonal_star (T : H →L[ℂ] H) :
    sequenceDiagonal (star T) = star (sequenceDiagonal T) := by
  change sequenceDiagonal (star T) = (sequenceDiagonal T).adjoint
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [lp.inner_eq_tsum, sequenceDiagonal_apply]
  exact tsum_congr (fun n => ContinuousLinearMap.adjoint_inner_left T (y n) (x n))

def sequenceDiagonalHom : (H →L[ℂ] H) →⋆ₐ[ℂ] (SequenceHilbert H →L[ℂ] SequenceHilbert H) where
  toFun := sequenceDiagonal
  map_zero' := by ext x n; rfl
  map_one' := by ext x n; rfl
  map_add' T U := by ext x n; rfl
  map_mul' T U := by ext x n; rfl
  commutes' c := by ext x n; rfl
  map_star' := sequenceDiagonal_star

def sequenceMatrixUnit (i j : ℕ) : SequenceHilbert H →L[ℂ] SequenceHilbert H :=
  (lp.singleContinuousLinearMap (𝕜 := ℂ) (E := fun _ : ℕ => H) 2 i).comp
    (lp.evalCLM ℂ (fun _ : ℕ => H) 2 j)

omit [CompleteSpace H] in
lemma sequenceMatrixUnit_apply (i j : ℕ) (x : SequenceHilbert H) (k : ℕ) :
    sequenceMatrixUnit i j x k = if k = i then x j else 0 := by
  change (lp.single (E := fun _ : ℕ => H) 2 i (x j)) k = _
  simp [lp.single_apply, Pi.single_apply]

omit [CompleteSpace H] in
lemma sequenceDiagonal_matrixUnit_commute (T : H →L[ℂ] H) (i j : ℕ) :
    Commute (sequenceDiagonal T) (sequenceMatrixUnit i j) := by
  apply (commute_iff_eq _ _).mpr
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  simp only [mul_apply_eq_comp, sequenceDiagonal_apply,
    sequenceMatrixUnit_apply]
  split_ifs <;> simp only [map_zero]

def sequenceEntryZero (T : SequenceHilbert H →L[ℂ] SequenceHilbert H) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 0).comp
    (T.comp (lp.singleContinuousLinearMap (𝕜 := ℂ) (E := fun _ : ℕ => H) 2 0))

omit [CompleteSpace H] in
lemma sequenceEntryZero_apply (T : SequenceHilbert H →L[ℂ] SequenceHilbert H) (x : H) :
    sequenceEntryZero T x = T (lp.single 2 0 x) 0 := rfl

omit [CompleteSpace H] in
lemma sequence_diagonal_of_matrixUnit_commutation
    (T : SequenceHilbert H →L[ℂ] SequenceHilbert H)
    (hT : ∀ i j, Commute (sequenceMatrixUnit (H := H) i j) T) :
    T = sequenceDiagonal (sequenceEntryZero T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  have h := congrArg (fun U : SequenceHilbert H →L[ℂ] SequenceHilbert H => U x 0)
    (hT 0 n).eq
  change T x n = T (lp.single (E := fun _ : ℕ => H) 2 0 (x n)) 0 at h
  exact h


variable {A : Type*} [CStarAlgebra A]

def sequenceAmplification (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₐ[ℂ] (SequenceHilbert H →L[ℂ] SequenceHilbert H) := sequenceDiagonalHom.comp π

lemma sequence_double_commutant_diagonal
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : SequenceHilbert H →L[ℂ] SequenceHilbert H)
    (hT : ∀ R : SequenceHilbert H →L[ℂ] SequenceHilbert H,
      (∀ a, Commute (sequenceAmplification π a) R) → Commute R T) :
    T = sequenceDiagonal (sequenceEntryZero T) := by
  apply sequence_diagonal_of_matrixUnit_commutation
  intro i j
  apply hT
  intro a
  exact sequenceDiagonal_matrixUnit_commute (π a) i j

end WeakPureInfiniteness

end

end OAI
