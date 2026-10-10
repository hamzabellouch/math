import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumYYElimination
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorAncilla

namespace OAI

/-! Exact Pauli words for the mediator flip and occupation matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaSinglePauliWord (i : ι) (a : Fin 4) : ι → Fin 4 := fun k => if k = i then a else 0

theorem qmaSinglePauliWord_apply (i : ι) (a : Fin 4) (s t : ι → Fin 2) :
    qmaPauliWord (qmaSinglePauliWord i a) s t =
      qmaPauli a (s i) (t i)*(∏ k ∈ Finset.univ.erase i, if s k = t k then (1:ℂ) else 0) := by
  rw [qmaPauliWord,← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [qmaSinglePauliWord,ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp [(Finset.mem_erase.mp hk).1,qmaPauli_zero,Matrix.one_apply]

theorem qmaSinglePauliWord_support (i : ι) (a : Fin 4) :
    qmaPauliSupport (qmaSinglePauliWord i a) ⊆ {i} := by
  intro k hk
  by_contra hn
  have hki : k ≠ i := by simpa using hn
  have ha := (Finset.mem_filter.mp hk).2
  simp [qmaSinglePauliWord,hki] at ha

theorem qmaSinglePauliWord_X (i : ι) :
    qmaPauliWord (qmaSinglePauliWord i 1) = qmaBitFlipMatrix i := by
  have hX (u v : Fin 2) : qmaPauli 1 u v =
      if u = Equiv.swap (0:Fin 2) 1 v then (1:ℂ) else 0 := by
    fin_cases u <;> fin_cases v <;> norm_num [qmaPauli,pauliX,Equiv.swap_apply_def]
  ext s t
  rw [qmaSinglePauliWord_apply,hX]
  change _ = if s = qmaBitFlip i t then (1:ℂ) else 0
  by_cases h : s = qmaBitFlip i t
  · subst s
    simp only [ite_true]
    have he : qmaBitFlip i t i = Equiv.swap (0:Fin 2) 1 (t i) := by simp [qmaBitFlip]
    rw [ite_eq_left he,one_mul]
    apply Finset.prod_eq_one
    intro k hk
    simp [qmaBitFlip,(Finset.mem_erase.mp hk).1]
  · rw [ite_eq_right h]
    obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    by_cases hki : k = i
    · subst k
      have he : s i ≠ Equiv.swap (0:Fin 2) 1 (t i) := by simpa [qmaBitFlip] using hk
      rw [ite_eq_right he,zero_mul]
    · have he : s k ≠ t k := by simpa [qmaBitFlip,hki] using hk
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩)
        (ite_eq_right he),mul_zero]

theorem qmaSinglePauliWord_Z (i : ι) :
    qmaPauliWord (qmaSinglePauliWord i 3) =
      Matrix.diagonal (fun s => if s i = 1 then (-1:ℂ) else 1) := by
  have hZ (u v : Fin 2) : qmaPauli 3 u v =
      if u = v then (if u = 1 then (-1:ℂ) else 1) else 0 := by
    fin_cases u <;> fin_cases v <;> norm_num [qmaPauli,pauliZ]
  ext s t
  rw [qmaSinglePauliWord_apply,hZ,Matrix.diagonal_apply]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    by_cases hki : k = i
    · subst k
      rw [ite_eq_right hk,zero_mul]
    · rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩)
        (ite_eq_right hk),mul_zero]

theorem qmaAncillaOccupation_pauli (i : ι) : qmaAncillaOccupation i =
    (1/2:ℂ) • (1-qmaPauliWord (qmaSinglePauliWord i 3)) := by
  rw [qmaSinglePauliWord_Z]
  ext s t
  by_cases h : s = t
  · subst t
    generalize hs : s i = v
    fin_cases v <;> norm_num [qmaAncillaOccupation,Matrix.diagonal_apply,Matrix.one_apply,hs]
  · simp [qmaAncillaOccupation,h]

end ContinuumCoulomb

end

end OAI
