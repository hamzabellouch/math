import OAI.Analysis.MutuallyUnbiased.Cubic.CubicExclusion
import OAI.Analysis.MutuallyUnbiased.Cubic.NormalizedCubic
import OAI.Analysis.MutuallyUnbiased.Matrix.Equivalence

namespace OAI

noncomputable section

namespace MUB6

/-- The cubic classification from the companion: no restriction is imposed
on the complex entries or on the unit phases in the equivalence relation. -/
theorem hadamard_square_equivalent_tao {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) : Equivalent H tao := by
  let D := dephase H
  have hD : IsHadamard D := dephase_isHadamard hH
  have hD2 : IsHadamard (fun i j => D i j ^ 2) := dephase_square_isHadamard hH hH2
  have hDr : ∀ j, D 0 j = 1 := dephase_row_zero hH
  have hDc : ∀ i, D i 0 = 1 := dephase_column_zero hH
  have hcube : ∀ i j, D i j ^ 3 = 1 := dephased_hadamard_cubes_one hD hD2 hDr hDc
  obtain ⟨p, hp⟩ := cubic_hadamard_one_matching hD hcube hDr hDc
  let K : CMatrix := fun i j => D i (fixZeroPermutation p j)
  have hK : IsHadamard K := by
    simpa only [Equiv.refl_apply] using hD.permutations (Equiv.refl _) (fixZeroPermutation p)
  have hKr : ∀ j, K 0 j = 1 := fun j => hDr _
  have hKc : ∀ i, K i 0 = 1 := fun i => hDc _
  have hKcube : ∀ i j, K i j ^ 3 = 1 := fun i j => hcube _ _
  have hdiag : ∀ i j : Fin 5, K i.succ j.succ = 1 ↔ i = j := hp
  have hDK : Equivalent D K := by
    refine ⟨Equiv.refl _, fixZeroPermutation p, fun _ => 1, fun _ => 1,
      by simp, by simp, ?_⟩
    intro i j
    simp [K]
  exact equivalent_trans (dephase_equivalent hH)
    (equivalent_trans hDK (normalized_cubic_equivalent_tao hK hKcube hKr hKc hdiag))

end MUB6

end

end OAI
