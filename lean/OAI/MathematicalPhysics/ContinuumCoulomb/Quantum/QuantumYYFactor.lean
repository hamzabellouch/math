import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliProduct
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEntryParity

namespace OAI

/-! A YY term is a product of commuting real XZ and ZX involutions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaTwoPauliWord (i j : ι) (a b : Fin 4) : ι → Fin 4 :=
  fun k => if k = i then a else if k = j then b else 0

theorem qmaTwoPauliWord_support (i j : ι) (a b : Fin 4) :
    qmaPauliSupport (qmaTwoPauliWord i j a b) ⊆ {i,j} := by
  intro k hk
  by_contra hn
  have hki : k ≠ i := fun h => hn (by simp [h])
  have hkj : k ≠ j := fun h => hn (by simp [h])
  have hz : qmaTwoPauliWord i j a b k ≠ 0 := (Finset.mem_filter.mp hk).2
  simp [qmaTwoPauliWord,hki,hkj] at hz

theorem qmaTwoPauliWord_real (i j : ι) (a b : Fin 4) (ha : a ≠ 2) (hb : b ≠ 2) :
    QMAEntryParity false (qmaPauliWord (qmaTwoPauliWord i j a b)) := by
  apply qmaPauliWord_real_of_even
  have hnoY (k : ι) : qmaTwoPauliWord i j a b k ≠ 2 := by
    unfold qmaTwoPauliWord
    split_ifs <;> simp_all
  have hz : qmaPauliYCount (qmaTwoPauliWord i j a b) = 0 := by
    simp [qmaPauliYCount,hnoY]
  rw [hz]
  norm_num

theorem qmaYY_factor (i j : ι) (hij : i ≠ j) :
    qmaPauliWord (qmaTwoPauliWord i j 1 3)*qmaPauliWord (qmaTwoPauliWord i j 3 1) =
      qmaPauliWord (qmaTwoPauliWord i j 2 2) := by
  rw [qmaPauliWord_product]
  have hindex : (fun k => qmaPauliProductIndex (qmaTwoPauliWord i j 1 3 k)
      (qmaTwoPauliWord i j 3 1 k)) = qmaTwoPauliWord i j 2 2 := by
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [qmaTwoPauliWord,qmaPauliProductIndex,hki,hkj,Ne.symm hij]
  rw [hindex]
  have hphase : (∏ k, qmaPauliProductPhase (qmaTwoPauliWord i j 1 3 k)
      (qmaTwoPauliWord i j 3 1 k)) = 1 := by
    rw [← Finset.prod_subset (Finset.subset_univ ({i,j} : Finset ι))]
    · simp [qmaTwoPauliWord,qmaPauliProductPhase,hij,Ne.symm hij]
    · intro k _ hk
      have hki : k ≠ i := fun h => hk (by simp [h])
      have hkj : k ≠ j := fun h => hk (by simp [h])
      simp [qmaTwoPauliWord,qmaPauliProductPhase,hki,hkj]
  rw [hphase,one_smul]

theorem qmaYY_factor_commute (i j : ι) (hij : i ≠ j) :
    qmaPauliWord (qmaTwoPauliWord i j 1 3)*qmaPauliWord (qmaTwoPauliWord i j 3 1) =
      qmaPauliWord (qmaTwoPauliWord i j 3 1)*qmaPauliWord (qmaTwoPauliWord i j 1 3) := by
  have h := congrArg Matrix.conjTranspose (qmaYY_factor i j hij)
  rw [Matrix.conjTranspose_mul,(qmaPauliWord_hermitian _).eq,
    (qmaPauliWord_hermitian _).eq,(qmaPauliWord_hermitian _).eq] at h
  exact (qmaYY_factor i j hij).trans h.symm

end ContinuumCoulomb

end

end OAI
