import OAI.Analysis.GroupDeterminants.GroupAlgebraStar

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace AverageDraft
section Algebra
variable {A : Type uA} [Ring A] [Algebra ℚ A]
def thirdAverage (z : A) : A := (1 / 3 : ℚ) • (1 + z + z * z)
lemma thirdAverage_square (z : A) (hz : z * z * z = 1) :
    thirdAverage z * thirdAverage z = thirdAverage z := by
  have hz4 : z * z * (z * z) = z := by rw [← mul_assoc, hz, one_mul]
  have he : (1 + z + z * z) * (1 + z + z * z) =
      (3 : ℚ) • (1 + z + z * z) := by
    calc
      _ = 1 + z + z + z * z + z * z + z * z +
          z * z * z + z * z * z + z * z * (z * z) := by noncomm_ring
      _ = _ := by rw [hz, hz4]; simp only [show (3 : ℚ) = 1 + 1 + 1 by norm_num,
        add_smul, one_smul]; abel
  simp only [thirdAverage, smul_mul_smul_comm, he, smul_smul]
  norm_num

lemma thirdAverage_commute (z w : A) (h : Commute z w) :
    Commute (thirdAverage z) (thirdAverage w) := by
  apply Commute.smul_left
  apply Commute.smul_right
  have h' : Commute (1 + z + z * z) w :=
    ((Commute.one_left _).add_left h).add_left (h.mul_left h)
  exact ((Commute.one_right _).add_right h').add_right (h'.mul_right h')
end Algebra
end AverageDraft

end

end OAI
