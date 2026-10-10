import OAI.Combinatorics.BalancedRyser.Local.LocalConditionFibers

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem indexedThrough_eq_of_unused_eq (a : DirectionAssignment F b κ)
    (M N : MergedPairs F)
    (h : ∀ d, d ∉ FourEvents.usedDirections a → M d = N d)
    (p : Point F) :
    indexedThrough M (unusedDirections a) p =
      indexedThrough N (unusedDirections a) p := by
  ext ds
  by_cases hd : ds.1 ∉ FourEvents.usedDirections a
  · simp [indexedThrough, unusedDirections, hd, constituent, h ds.1 hd]
  · simp [indexedThrough, unusedDirections, hd]

theorem pointHolds_iff_of_unused_eq (a : DirectionAssignment F b κ)
    (p : Point F) (M N : MergedPairs F)
    (h : ∀ d, d ∉ FourEvents.usedDirections a → M d = N d)
    (x : Position b → Point F) (v : Position b) (z : Code b κ) :
    PointHolds a p M x v z ↔ PointHolds a p N x v z := by
  rcases z with z | xy | w | cw
  · simp only [PointHolds]
    apply exists_congr
    intro d
    by_cases hd : d ∉ FourEvents.usedDirections a
    · simp only [hd, constituent, h d hd]
    · simp only [hd, false_and]
  · rfl
  · simp only [PointHolds]
    apply exists_congr
    intro d
    by_cases hd : d ∉ FourEvents.usedDirections a
    · simp only [hd, mergedPoints, constituent, h d hd]
    · simp only [hd, false_and]
  · rfl

theorem holds_iff_pointHolds_of_unused_eq (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M N : MergedPairs F)
    (h : ∀ d, d ∉ FourEvents.usedDirections a → M d = N d)
    (v : Position b) (z : Code b κ) :
    Holds P a bits p M v z ↔
      PointHolds a p N (prescribedPoint P a bits M) v z := by
  rw [holds_eq_pointHolds]
  exact pointHolds_iff_of_unused_eq a p M N h _ v z

end
end Balanced.Local.ConditionSpec

end OAI
