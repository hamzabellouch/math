import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnitaryGround
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalJoin
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorNorm

namespace OAI

/-! A diagonal unitary rotates any chosen mediator X couplings to Y. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def qmaPhaseFactor (m : Bool) (a : Fin 2) : ℂ :=
  if m = true ∧ a = 1 then -Complex.I else 1

theorem qmaPhaseFactor_gram (m : Bool) (a : Fin 2) :
    star (qmaPhaseFactor m a)*qmaPhaseFactor m a = 1 := by
  cases m <;> fin_cases a <;> norm_num [qmaPhaseFactor]

theorem qmaPhaseFactor_flip (m : Bool) (a : Fin 2) :
    star (qmaPhaseFactor m (Equiv.swap (0:Fin 2) 1 a))*qmaPhaseFactor m a =
      if m = true then (if a = 1 then -Complex.I else Complex.I) else 1 := by
  cases m <;> fin_cases a <;> norm_num [qmaPhaseFactor]

def qmaAncillaPhase (m : κ → Bool) (a : κ → Fin 2) : ℂ := ∏ e, qmaPhaseFactor (m e) (a e)

omit [DecidableEq κ] in
theorem qmaAncillaPhase_gram (m : κ → Bool) (a : κ → Fin 2) :
    star (qmaAncillaPhase m a)*qmaAncillaPhase m a = 1 := by
  simp only [qmaAncillaPhase,star_prod,← Finset.prod_mul_distrib,qmaPhaseFactor_gram,Finset.prod_const_one]

def qmaPhaseMatrix (m : κ → Bool) : Matrix (κ → Fin 2) (κ → Fin 2) ℂ :=
  Matrix.diagonal (qmaAncillaPhase m)

theorem qmaPhaseMatrix_gram (m : κ → Bool) : (qmaPhaseMatrix m).conjTranspose*qmaPhaseMatrix m = 1 := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [qmaPhaseMatrix,Matrix.mul_apply,Matrix.diagonal_apply]
    exact qmaAncillaPhase_gram m a
  · simp [qmaPhaseMatrix,Matrix.mul_apply,Matrix.diagonal_apply,h]

theorem qmaPhaseMatrix_cogram (m : κ → Bool) : qmaPhaseMatrix m*(qmaPhaseMatrix m).conjTranspose = 1 := by
  ext a b
  by_cases h : a = b
  · subst b
    simpa [qmaPhaseMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
      mul_comm] using qmaAncillaPhase_gram m a
  · simp [qmaPhaseMatrix,Matrix.mul_apply,Matrix.diagonal_apply,h]

theorem qmaAncillaPhase_flip (m : κ → Bool) (e : κ) (b : κ → Fin 2) :
    star (qmaAncillaPhase m (qmaBitFlip e b))*qmaAncillaPhase m b =
      if m e = true then (if b e = 1 then -Complex.I else Complex.I) else 1 := by
  unfold qmaAncillaPhase
  rw [star_prod,← Finset.prod_mul_distrib,Finset.prod_eq_single e]
  · simpa only [qmaBitFlip,Function.update_self] using qmaPhaseFactor_flip (m e) (b e)
  · intro f _ hfe
    simp only [qmaBitFlip,Function.update_of_ne hfe]
    exact qmaPhaseFactor_gram (m f) (b f)
  · intro h
    exact False.elim (h (Finset.mem_univ e))

def qmaPolarizedFlip (m : κ → Bool) (e : κ) : Matrix (κ → Fin 2) (κ → Fin 2) ℂ :=
  fun a b => if a = qmaBitFlip e b then
    (if m e = true then (if b e = 1 then -Complex.I else Complex.I) else 1) else 0

theorem qmaDiagonal_sandwich {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℂ) (M : Matrix α α ℂ) (a b : α) :
    ((Matrix.diagonal f).conjTranspose*M*Matrix.diagonal f) a b = star (f a)*M a b*f b := by
  simp [Matrix.mul_apply,Matrix.diagonal_apply]

theorem qmaPhaseMatrix_flip (m : κ → Bool) (e : κ) :
    (qmaPhaseMatrix m).conjTranspose*qmaBitFlipMatrix e*qmaPhaseMatrix m = qmaPolarizedFlip m e := by
  ext a b
  rw [qmaPhaseMatrix,qmaDiagonal_sandwich]
  by_cases h : a = qmaBitFlip e b
  · subst a
    simp only [qmaBitFlipMatrix,qmaPolarizedFlip,ite_true,mul_one]
    exact qmaAncillaPhase_flip m e b
  · simp [qmaBitFlipMatrix,qmaPolarizedFlip,h]

theorem qmaPhaseMatrix_diagonal (m : κ → Bool) (d : (κ → Fin 2) → ℂ) :
    (qmaPhaseMatrix m).conjTranspose*Matrix.diagonal d*qmaPhaseMatrix m = Matrix.diagonal d := by
  ext a b
  rw [qmaPhaseMatrix,qmaDiagonal_sandwich]
  by_cases h : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq]
    calc
      _ = (star (qmaAncillaPhase m a)*qmaAncillaPhase m a)*d a := by ring
      _ = _ := by rw [qmaAncillaPhase_gram,one_mul]
  · simp [h]

end ContinuumCoulomb

end

end OAI
