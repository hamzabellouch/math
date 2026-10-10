import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalAction

namespace OAI

/-! Occupation coordinates for the parallel qubit mediator gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def qmaAncillaVacuum : κ → Fin 2 := fun _ => 0

def qmaAncillaSingle (e : κ) : κ → Fin 2 := Function.update qmaAncillaVacuum e 1

omit [Fintype κ] in
theorem qmaAncillaSingle_apply (e f : κ) :
    qmaAncillaSingle e f = if f = e then 1 else 0 := by
  simp [qmaAncillaSingle,qmaAncillaVacuum,Function.update_apply]

omit [Fintype κ] in
theorem qmaAncillaSingle_ne_vacuum (e : κ) : qmaAncillaSingle e ≠ qmaAncillaVacuum := by
  intro h
  have he := congrFun h e
  simp [qmaAncillaSingle,qmaAncillaVacuum] at he

omit [Fintype κ] in
theorem qmaAncillaSingle_injective : Function.Injective (qmaAncillaSingle (κ := κ)) := by
  intro e f h
  by_contra hef
  have he := congrFun h e
  simp [qmaAncillaSingle_apply,hef] at he

omit [Fintype κ] in
theorem qmaBitFlip_vacuum (e : κ) : qmaBitFlip e qmaAncillaVacuum = qmaAncillaSingle e := by
  simp [qmaBitFlip,qmaAncillaSingle,qmaAncillaVacuum]

omit [Fintype κ] in
theorem qmaBitFlip_single_self (e : κ) : qmaBitFlip e (qmaAncillaSingle e) = qmaAncillaVacuum := by
  rw [← qmaBitFlip_vacuum,qmaBitFlip_involutive]

omit [Fintype κ] in
theorem qmaBitFlip_single_ne_single (e f d : κ) :
    qmaAncillaSingle e ≠ qmaBitFlip f (qmaAncillaSingle d) := by
  intro h
  by_cases hfd : f = d
  · subst f
    rw [qmaBitFlip_single_self] at h
    exact qmaAncillaSingle_ne_vacuum e h
  · have hf := congrFun h f
    have hd := congrFun h d
    by_cases hef : e = f
    · subst e
      simp [qmaAncillaSingle_apply,qmaBitFlip,hfd,Ne.symm hfd] at hd
    · simp [qmaAncillaSingle_apply,qmaBitFlip,Ne.symm hef,hfd] at hf

def qmaAncillaNumber (a : κ → Fin 2) : ℕ := ∑ e, (a e).val

omit [DecidableEq κ] in
@[simp] theorem qmaAncillaNumber_vacuum :
    qmaAncillaNumber (qmaAncillaVacuum (κ := κ)) = 0 := by
  simp [qmaAncillaNumber,qmaAncillaVacuum]

@[simp] theorem qmaAncillaNumber_single (e : κ) :
    qmaAncillaNumber (qmaAncillaSingle e) = 1 := by
  simp [qmaAncillaNumber,qmaAncillaSingle_apply,apply_ite]

omit [DecidableEq κ] in
theorem qmaAncillaNumber_pos (a : κ → Fin 2) (ha : a ≠ qmaAncillaVacuum) :
    0 < qmaAncillaNumber a := by
  by_contra h
  have hz : qmaAncillaNumber a = 0 := by omega
  apply ha
  funext e
  have he : (a e).val ≤ qmaAncillaNumber a :=
    Finset.single_le_sum (f := fun i => (a i).val) (fun i _ => Nat.zero_le _) (Finset.mem_univ e)
  apply Fin.ext
  change (a e).val = 0
  omega

def qmaAncillaOccupation (e : κ) : Matrix (κ → Fin 2) (κ → Fin 2) ℂ :=
  Matrix.diagonal (fun a => if a e = 1 then 1 else 0)

theorem qmaAncillaOccupation_single (e f d : κ) :
    qmaAncillaOccupation e (qmaAncillaSingle f) (qmaAncillaSingle d) =
      if f = d ∧ e = d then 1 else 0 := by
  unfold qmaAncillaOccupation
  rw [Matrix.diagonal_apply]
  by_cases hfd : f = d
  · subst f
    by_cases hed : e = d <;> simp [hed,qmaAncillaSingle_apply]
  · have hn := (Function.Injective.ne qmaAncillaSingle_injective hfd)
    simp [hfd,hn]

theorem qmaBitFlipMatrix_single (e f d : κ) :
    qmaBitFlipMatrix e (qmaAncillaSingle f) (qmaAncillaSingle d) = 0 := by
  exact ite_eq_right (qmaBitFlip_single_ne_single f e d)

theorem qmaBitFlipMatrix_vacuum_right (e : κ) (a : κ → Fin 2) :
    qmaBitFlipMatrix e a qmaAncillaVacuum = if a = qmaAncillaSingle e then 1 else 0 := by
  rw [qmaBitFlipMatrix,qmaBitFlip_vacuum]

omit [DecidableEq κ] in
theorem qmaAncillaOccupation_vacuum_right (e : κ) (a : κ → Fin 2) :
    qmaAncillaOccupation e a qmaAncillaVacuum = 0 := by
  by_cases ha : a = qmaAncillaVacuum
  · subst a
    simp [qmaAncillaOccupation,qmaAncillaVacuum]
  · simp [qmaAncillaOccupation,ha]

end ContinuumCoulomb

end

end OAI
