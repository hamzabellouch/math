import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliExtend

namespace OAI

/-! A bounded-support real family expands into only even-Y Pauli words. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

abbrev QMALocalPauliTerm (S : α → Finset ι) :=
  (a : α) × ({i // i ∈ S a} → Fin 4)

abbrev QMALocalEvenPauliTerm (S : α → Finset ι) :=
  {p : QMALocalPauliTerm S // Even (qmaPauliYCount p.2)}

def qmaLocalPauliWord (S : α → Finset ι) (p : QMALocalPauliTerm S) : ι → Fin 4 :=
  qmaPauliExtend (S p.1) p.2

def qmaLocalPauliCoefficient (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : α → Finset ι) (p : QMALocalPauliTerm S) : ℝ :=
  (qmaPauliCoefficient (qmaLocalCore (S p.1) (F p.1)) p.2).re

def qmaLocalPauliMatrix (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : α → Finset ι) (p : QMALocalPauliTerm S) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  (qmaLocalPauliCoefficient F S p : ℂ) • qmaPauliWord (qmaLocalPauliWord S p)

theorem qmaLocalPauli_sum (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : α → Finset ι) (hF : ∀ a, QMALocalOn (S a) (F a)) (hH : ∀ a, (F a).IsHermitian) :
    (∑ p : QMALocalPauliTerm S, qmaLocalPauliMatrix F S p) = ∑ a, F a := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  simp only [qmaLocalPauliMatrix,qmaLocalPauliWord,qmaPauliExtend_lift]
  exact (hF a).pauli_expansion (hH a)

omit [Fintype α] in
theorem qmaLocalPauli_odd_zero (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : α → Finset ι) (hH : ∀ a, (F a).IsHermitian)
    (hR : ∀ a, QMAEntryParity false (F a)) (p : QMALocalPauliTerm S)
    (hp : Odd (qmaPauliYCount p.2)) : qmaLocalPauliMatrix F S p = 0 := by
  have he := qmaPauliCoefficient_odd_zero (qmaLocalCore (S p.1) (F p.1))
    (qmaLocalCore_hermitian _ _ (hH p.1)) (qmaLocalCore_real _ _ (hR p.1)) p.2 hp
  simp only [qmaLocalPauliMatrix,qmaLocalPauliCoefficient,he,Complex.zero_re,
    Complex.ofReal_zero,zero_smul]

theorem qmaLocalEvenPauli_sum (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : α → Finset ι) (hF : ∀ a, QMALocalOn (S a) (F a)) (hH : ∀ a, (F a).IsHermitian)
    (hR : ∀ a, QMAEntryParity false (F a)) :
    (∑ p : QMALocalEvenPauliTerm S, qmaLocalPauliMatrix F S p.val) = ∑ a, F a := by
  rw [← qmaLocalPauli_sum F S hF hH]
  let T : Finset (QMALocalPauliTerm S) := Finset.univ.filter (fun p => Even (qmaPauliYCount p.2))
  have hsub := Finset.sum_subtype (F := inferInstance) T
    (by simp [T] : ∀ p, p ∈ T ↔ Even (qmaPauliYCount p.2)) (qmaLocalPauliMatrix F S)
  rw [← hsub]
  apply Finset.sum_subset (Finset.subset_univ T)
  intro p _ hp
  have hn : ¬Even (qmaPauliYCount p.2) := by simpa [T] using hp
  exact qmaLocalPauli_odd_zero F S hH hR p ((Nat.even_or_odd _).resolve_left hn)

omit [Fintype ι] in
theorem qmaLocalEvenPauli_count (S : α → Finset ι) {d : ℕ} (hS : ∀ a, (S a).card ≤ d) :
    Fintype.card (QMALocalEvenPauliTerm S) ≤ 4^d*Fintype.card α := by
  apply (Fintype.card_subtype_le _).trans
  calc
    Fintype.card (QMALocalPauliTerm S) = ∑ a : α, 4^(S a).card := by
      simp only [QMALocalPauliTerm,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin,
        Fintype.card_coe]
    _ ≤ ∑ _a : α, 4^d := Finset.sum_le_sum (fun a _ =>
      pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 4) (hS a))
    _ = _ := by simp [Nat.mul_comm]

omit [Fintype α] in
theorem qmaLocalEvenPauli_support (S : α → Finset ι) {d : ℕ}
    (hS : ∀ a, (S a).card ≤ d) (p : QMALocalEvenPauliTerm S) :
    (qmaPauliSupport (qmaLocalPauliWord S p.val)).card ≤ d :=
  (Finset.card_le_card (qmaPauliExtend_support _ _)).trans (hS p.val.1)

omit [Fintype α] in
theorem qmaLocalEvenPauli_even (S : α → Finset ι) (p : QMALocalEvenPauliTerm S) :
    Even (qmaPauliYCount (qmaLocalPauliWord S p.val)) := by
  rw [qmaLocalPauliWord,qmaPauliExtend_yCount]
  exact p.property

end ContinuumCoulomb

end

end OAI
