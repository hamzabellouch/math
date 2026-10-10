import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliReal

namespace OAI

/-! The small support matrix is recovered canonically by fixing every
spectator qubit to zero, preserving real entries and Hermiticity. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaLocalCore (S : Finset ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ :=
  A.submatrix (qmaSupportExtend S) (qmaSupportExtend S)

theorem qmaLocalCore_lift (S : Finset ι)
    (B : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalCore S (qmaLocalLift S B) = B := by
  ext u v
  change qmaLocalLift S B (qmaSupportExtend S u) (qmaSupportExtend S v) = B u v
  rw [qmaLocalLift_apply]
  have hs (u : QMASupportBasis S) :
      (fun i : {i // i ∈ S} => qmaSupportExtend S u i.val) = u := by
    funext i
    simp [qmaSupportExtend,i.property]
  have hr : (fun i : {i // i ∉ S} => qmaSupportExtend S u i.val) =
      (fun i : {i // i ∉ S} => qmaSupportExtend S v i.val) := by
    funext i
    simp [qmaSupportExtend,i.property]
  rw [hs,hs,ite_eq_left hr,mul_one]

theorem QMALocalOn.core_lift {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) : qmaLocalLift S (qmaLocalCore S A) = A := by
  obtain ⟨B,rfl⟩ := hA
  rw [qmaLocalCore_lift]

omit [Fintype ι] in
theorem qmaLocalCore_hermitian (S : Finset ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : A.IsHermitian) : (qmaLocalCore S A).IsHermitian :=
  hA.submatrix (qmaSupportExtend S)

omit [Fintype ι] in
theorem qmaLocalCore_real (S : Finset ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : ∀ s t, (A s t).im = 0) (u v : QMASupportBasis S) :
    (qmaLocalCore S A u v).im = 0 := hA _ _

theorem qmaLocalLift_zero (S : Finset ι) :
    qmaLocalLift S (0 : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) = 0 := by
  ext s t
  simp [qmaLocalLift_apply]

theorem qmaLocalLift_sum {κ : Type*} [Fintype κ] (S : Finset ι)
    (B : κ → Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S (∑ i, B i) = ∑ i, qmaLocalLift S (B i) := by
  have hs (s : Finset κ) : qmaLocalLift S (∑ i ∈ s, B i) = ∑ i ∈ s, qmaLocalLift S (B i) := by
    induction s using Finset.induction_on with
    | empty => simp [qmaLocalLift_zero]
    | @insert a s ha ih => simp only [Finset.sum_insert ha,qmaLocalLift_add,ih]
  exact hs Finset.univ

theorem QMALocalOn.pauli_expansion {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hH : A.IsHermitian) :
    (∑ w : {i // i ∈ S} → Fin 4,
      ((qmaPauliCoefficient (qmaLocalCore S A) w).re : ℂ) •
        qmaLocalLift S (qmaPauliWord w)) = A := by
  have he := qmaPauli_real_expansion (qmaLocalCore S A) (qmaLocalCore_hermitian S A hH)
  have h := congrArg (qmaLocalLift S) he
  rw [qmaLocalLift_sum] at h
  simp only [qmaLocalLift_smul] at h
  exact h.trans hA.core_lift

end ContinuumCoulomb

end

end OAI
