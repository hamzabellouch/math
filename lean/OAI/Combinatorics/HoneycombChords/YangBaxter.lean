import OAI.Combinatorics.HoneycombChords.YangBaxterPositive
import OAI.Combinatorics.HoneycombChords.YangBaxterZero
import OAI.Combinatorics.HoneycombChords.YangBaxterNegative
import OAI.Combinatorics.HoneycombChords.YangBaxterWeights

namespace OAI

/-! The honeycomb Yang–Baxter identity in the sine parametrization.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/

namespace CriticalHoneycomb.Transfer.YangBaxter
open scoped BigOperators

section Algebra
variable (C A S x y z w ii : ℂ)
variable (hC : C = (2*S+1)*A) (hA : A^2 = (1-S)/2)
  (hS : S^2 = 1/2) (hy : y^2+x^2=1) (hw : w^2+z^2=1) (hi : ii^2+1=0)

include hC hA hS hy hw hi in
theorem numerator_yang_baxter (a b c d e f : Fin 3) :
  leftComponent C A S x y z w ii a b c d e f =
  rightComponent C A S x y z w ii a b c d e f := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exact block_000 C A S x y z w ii d e f
  · exact block_001 C A S x y z w ii hC hA hS hy hw d e f
  · exact block_002 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_010 C A S x y z w ii hy d e f
  · exact block_011 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_012 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_020 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_021 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_022 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_100 C A S x y z w ii hC hA hS hy hw d e f
  · exact block_101 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_102 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_110 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_111 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_112 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_120 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_121 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_122 C A S x y z w ii hC hA hS hy hw d e f
  · exact block_200 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_201 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_202 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_210 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_211 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_212 C A S x y z w ii hy d e f
  · exact block_220 C A S x y z w ii hC hA hS hy hw hi d e f
  · exact block_221 C A S x y z w ii hC hA hS hy hw d e f
  · exact block_222 C A S x y z w ii d e f

end Algebra

theorem source_yang_baxter (u v : ℝ)
    (hu : denominator u ≠ 0) (hv : denominator v ≠ 0)
    (hd : denominator (u-v) ≠ 0) (a b c d e f : Fin 3) :
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      sourceR (u-v) (a,b) (j,k) * sourceR u (j,c) (d,l) *
      sourceR v (k,l) (e,f)) =
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      sourceR v (b,c) (k,l) * sourceR u (a,l) (j,f) *
      sourceR (u-v) (j,k) (d,e)) := by
  rw [physical_left_sum _ _ hu hv hd, physical_right_sum _ _ hu hv hd]
  obtain ⟨hC,hA,hS,hy,hw,hi⟩ := trig_constraints u v
  rw [numerator_yang_baxter _ _ _ _ _ _ _ _ hC hA hS hy hw hi]

end CriticalHoneycomb.Transfer.YangBaxter

end OAI
