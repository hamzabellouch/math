import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFamilyAccuracy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZPrivate

namespace OAI

/-! Explicit scalar, one-site and two-site terms for the X/Z circuit family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaXZLabel (a : Fin 2) : Fin 4 := if a = 0 then 1 else 3

theorem qmaXZLabel_exists (i : Fin 4) (hi : i ≠ 0) (hy : i ≠ 2) :
    ∃ a : Fin 2, qmaXZLabel a = i := by
  fin_cases i
  · exact (hi rfl).elim
  · exact ⟨0,rfl⟩
  · exact (hy rfl).elim
  · exact ⟨1,rfl⟩

theorem qmaXZLabel_pauli (a : Fin 2) : qmaPauli (qmaXZLabel a) = qmaFourAxis a := by
  fin_cases a <;> rfl

inductive QMAXZTerm (n : ℕ) where
  | scalar
  | field (i : Fin n) (a : Fin 2)
  | pair (i j : Fin n) (hij : i ≠ j) (a b : Fin 2)

def QMAXZTerm.word {n : ℕ} : QMAXZTerm n → Fin n → Fin 4
  | .scalar => fun _ => 0
  | .field i a => fun k => if k = i then qmaXZLabel a else 0
  | .pair i j _ a b => fun k => if k = i then qmaXZLabel a else if k = j then qmaXZLabel b else 0

def QMAXZTerm.matrix {n : ℕ} : QMAXZTerm n → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  | .scalar => 1
  | .field i a => qmaSiteMatrix i (qmaFourAxis a)
  | .pair i j _ a b => qmaPairMatrix i j (qmaFourAxis a) (qmaFourAxis b)

theorem QMAXZTerm.word_matrix {n : ℕ} (t : QMAXZTerm n) : qmaPauliWord t.word = t.matrix := by
  change qmaTensorMatrix (fun k => qmaPauli (t.word k)) = _
  cases t with
  | scalar =>
    simpa only [QMAXZTerm.word,QMAXZTerm.matrix,qmaPauli_zero] using qmaTensorMatrix_one (Q := Fin n) (σ := Fin 2)
  | field i a =>
    change qmaTensorMatrix _ = qmaSiteMatrix i (qmaFourAxis a)
    rw [qmaSiteMatrix]
    congr 1
    funext k
    by_cases h : k = i <;> simp only [QMAXZTerm.word,h,ite_true,ite_false,qmaXZLabel_pauli,qmaPauli_zero]
  | pair i j hij a b =>
    change qmaTensorMatrix _ = qmaPairMatrix i j (qmaFourAxis a) (qmaFourAxis b)
    rw [qmaPairMatrix]
    congr 1
    funext k
    by_cases hi : k = i
    · simp only [QMAXZTerm.word,hi,ite_true,qmaXZLabel_pauli]
    · by_cases hj : k = j
      · subst k
        simp only [QMAXZTerm.word,hi,ite_true,ite_false,qmaXZLabel_pauli]
      · simp only [QMAXZTerm.word,hi,hj,ite_false,qmaPauli_zero]

theorem qmaXZWord_term {n : ℕ} (w : Fin n → Fin 4)
    (hy : ∀ i, w i ≠ 2) (hw : (qmaPauliSupport w).card ≤ 2) :
    ∃ t : QMAXZTerm n, t.word = w := by
  have hout (i : Fin n) (hi : i ∉ qmaPauliSupport w) : w i = 0 := by
    simpa only [qmaPauliSupport,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hi
  have hin (i : Fin n) (hi : i ∈ qmaPauliSupport w) : w i ≠ 0 :=
    (Finset.mem_filter.mp hi).2
  have hcases : (qmaPauliSupport w).card = 0 ∨ (qmaPauliSupport w).card = 1 ∨
      (qmaPauliSupport w).card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hz := Finset.card_eq_zero.mp hzero
    refine ⟨.scalar,?_⟩
    funext i
    exact (hout i (by simp [hz])).symm
  · obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hone
    obtain ⟨a,ha⟩ := qmaXZLabel_exists (w i) (hin i (by rw [hi]; exact Finset.mem_singleton_self i)) (hy i)
    refine ⟨.field i a,?_⟩
    funext k
    by_cases hk : k = i
    · subst k
      simpa only [QMAXZTerm.word,ite_true] using ha
    · simpa only [QMAXZTerm.word,hk,ite_false] using
        (hout k (by simpa only [hi,Finset.mem_singleton] using hk)).symm
  · obtain ⟨i,j,hij,hijset⟩ := Finset.card_eq_two.mp htwo
    obtain ⟨a,ha⟩ := qmaXZLabel_exists (w i) (hin i (by rw [hijset]; simp)) (hy i)
    obtain ⟨b,hb⟩ := qmaXZLabel_exists (w j) (hin j (by rw [hijset]; simp)) (hy j)
    refine ⟨.pair i j hij a b,?_⟩
    funext k
    by_cases hki : k = i
    · subst k
      simpa only [QMAXZTerm.word,ite_true] using ha
    · by_cases hkj : k = j
      · subst k
        simpa only [QMAXZTerm.word,Ne.symm hij,ite_false,ite_true] using hb
      · simpa only [QMAXZTerm.word,hki,hkj,ite_false] using (hout k (by simp [hijset,hki,hkj])).symm

end ContinuumCoulomb

end

end OAI
