import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineUniform

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset Variation

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
lemma qaverage_imageLaw (f : A→B) (h : B→ℚ) :
    ((qaverage (fun a=>h (f a)) : ℚ):ℝ)=∑ b,imageLaw f b*(h b:ℝ) := by
  classical
  unfold imageLaw push uniform
  simp only [sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq,mem_univ,ite_true,one_div,inv_mul_eq_div]
  unfold qaverage
  push_cast
  rw [sum_div]
lemma qaverage_eq_of_imageLaw_eq (f : A→C) (g : B→C)
    (he : imageLaw f=imageLaw g) (h : C→ℚ) :
    qaverage (fun a=>h (f a))=qaverage (fun b=>h (g b)) := by
  apply Rat.cast_injective (α:=ℝ)
  rw [qaverage_imageLaw,qaverage_imageLaw,he]
end MatchingFPRAS.PhysicalStream

end OAI
