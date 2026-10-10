import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction

variable {p q : ℕ}

lemma family_contract (m : Multiplicities p q) (j : Index m) (s t : Interval) :
    |(family m j s).1-(family m j t).1| ≤ |s.1-t.1|/2 := by
  rcases j with j|(j|j)
  · change |s.1/2-t.1/2|≤_
    rw [←sub_div,abs_div]; norm_num
  · change |(s.1+1)/2-(t.1+1)/2|≤_
    rw [← sub_div, add_sub_add_right_eq_sub, abs_div]
    norm_num
  · change |(1/2:ℝ)-1/2|≤_
    simp only [sub_self,abs_zero]
    positivity

end OriginalJiangSu

end

end OAI
