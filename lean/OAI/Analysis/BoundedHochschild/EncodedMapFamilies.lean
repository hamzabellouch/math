import OAI.Analysis.BoundedHochschild.LeftSandwichAverages

namespace OAI

/-! Orthogonal isometry columns encode finitely many maps into a single map.
Each map is recovered using only input and output left multiplication. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ}

def encodeMapFamily (c : Fin n → PartialIso M) (T : Fin n → M →L[ℂ] M) : M →L[ℂ] M :=
  ∑ i, leftSandwichMap (c i : M) (star (c i : M)) (T i)

omit [PartialOrder M] [StarOrderedRing M] in
lemma extract_encodeMapFamily (c : Fin n → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (T : Fin n → M →L[ℂ] M) (j : Fin n) :
    leftSandwichMap (star (c j : M)) (c j : M) (encodeMapFamily c T) = T j := by
  ext x
  simp only [leftSandwichMap_apply, encodeMapFamily, sum_apply]
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single j]
  · simp only [← mul_assoc, column_star_mul c hi ho, ite_true, one_mul]
  · intro i _ hij
    rw [← mul_assoc, column_star_mul c hi ho j i]
    simp only [Ne.symm hij, ite_false, zero_mul]
  · intro h
    exact (h (Finset.mem_univ j)).elim

lemma encodeMapFamily_completelyBounded (c : Fin n → PartialIso M)
    (T : Fin n → M →L[ℂ] M) (C : Fin n → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    CompletelyBoundedEstimate (encodeMapFamily c T)
      (∑ i, ‖(c i : M)‖ * C i * ‖star (c i : M)‖) :=
  completelyBounded_sum _ _ (fun i => completelyBounded_leftSandwich _ _ (hT i))

end BoundedHochschild.KadisonRingrose

end

end OAI
