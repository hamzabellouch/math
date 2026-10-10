import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordSplits

namespace OAI

/-! # Vanishing below the degree of an augmentation-ideal power -/

noncomputable section
namespace PolycyclicRecognition

variable {n : ℕ}

def WordMinimumDegree (p : RationalWords n) (k : ℕ) : Prop :=
  ∀ w, w.length < k → p.coeff w = 0

theorem WordMinimumDegree.mul {p q : RationalWords n} {k l : ℕ}
    (hp : WordMinimumDegree p k) (hq : WordMinimumDegree q l) :
    WordMinimumDegree (p * q) (k + l) := by
  intro w hw
  rw [word_coeff_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hlen : (wordSplit w i).1.length + (wordSplit w i).2.length = w.length := by
    rw [← FreeMonoid.length_mul, wordSplit_mul]
  by_cases hi : (wordSplit w i).1.length < k
  · rw [hp _ hi, zero_mul]
  · have hj : (wordSplit w i).2.length < l := by omega
    rw [hq _ hj, mul_zero]

theorem wordMinimumDegree_one_of_emptyCoeff {p : RationalWords n} (hp : p.coeff 1 = 0) :
    WordMinimumDegree p 1 := by
  intro w hw
  have hz : w.length = 0 := by omega
  have he : w = 1 := FreeMonoid.length_eq_zero.mp hz
  simpa only [he] using hp

theorem wordMinimumDegree_pow {p : RationalWords n} (hp : p.coeff 1 = 0) (k : ℕ) :
    WordMinimumDegree (p ^ k) k := by
  induction k with
  | zero => intro w hw; omega
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul (wordMinimumDegree_one_of_emptyCoeff hp)

end PolycyclicRecognition

end

end OAI
