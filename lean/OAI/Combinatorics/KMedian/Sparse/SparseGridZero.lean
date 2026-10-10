import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseBundleLaw

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open RationalWeightedStep (point)
variable {n : ℕ}

theorem zero (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (i : Fin n) (hi : q i=0)
    (a : Fin (law q).length) : (law q).states[a.val] i=0 := by
  have hb : base q i=0 := by simp only [base,hi,Nat.floor_zero]
  have hf : point (fraction q) i=0 := by
    simp only [fraction,point,Vector.getElem_ofFn,hi,hb,Nat.cast_zero,sub_zero]
  change Fin (SparseCardinalRounding.round (fraction q)).length at a
  have hz := SparseCardinalRounding.zero_fixed (fraction q) (fraction_unit q hq) i hf a
  have he := SparseIntegerLaw.map_states (SparseCardinalRounding.round (fraction q)) (count q) a
  change (law q).states[a.val]=_ at he
  rw [he]
  simp only [count,hz,zero_ne_one,ite_false,hb,Nat.add_zero]

end MetricKMedian.SparseGridRounding

namespace MetricKMedian.SparseBundles
variable {n m : ℕ}

theorem zero (q : Fin n → Fin m → ℚ) (hq : ∀ i j, 0 ≤ q i j)
    (a : Fin (law q).length) (i : Fin n) (j : Fin m) (hi : q i j=0) :
    (law q).states[a.val] j i=0 := by
  have hh := SparseCounts.run_columns (fun j => SparseGridRounding.law (fun i => q i j))
    (fun j S => ∀ i,q i j=0 → S i=0)
    (fun j a i hi => SparseGridRounding.zero (fun i => q i j) (fun i => hq i j) i hi a)
    m le_rfl a j j.isLt
  exact hh i hi

end MetricKMedian.SparseBundles
end
end

end OAI
