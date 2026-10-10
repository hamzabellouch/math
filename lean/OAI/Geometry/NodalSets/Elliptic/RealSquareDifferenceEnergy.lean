import OAI.Geometry.NodalSets.Elliptic.RealSquareCutoffEnergy

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_square_difference_test_energy {n : ℕ}
    (eta u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (R0 r : ℝ) (hr : r ≤ R0) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hb : ∀ x, |eta x| ≤ 1) (hs : tsupport eta ⊆ realCenteredCube n r)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R0 →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g j x*psi x))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R0-r) :
    let q := realDifferenceQuotient i h u
    let T := fun j x ↦ eta x*realDifferenceQuotient i h (g j) x
    let R := fun j x ↦ coordPartial eta x j*q x
    let P := realSquareCutoffGradient eta q (fun j ↦ realDifferenceQuotient i h (g j))
    let v := realSquareCutoff eta q
    let b := realDifferenceQuotient i (-h) v
    (∀ j, MemLp (T j) 2 volume ∧ MemLp (R j) 2 volume ∧ MemLp (P j) 2 volume) ∧
    MemLp b 2 volume ∧
    (∑ j, ∫ x, (P j x)^2) ≤ 2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) ∧
    (∫ x, (b x)^2) ≤ 2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) := by
  dsimp only
  have hq := realDifferenceQuotient_memLp i h u hu
  have hV (j : Fin n) := realDifferenceQuotient_memLp i h (g j) (hg j)
  have henergy := real_square_cutoff_gradient_energy eta _ _ he hc hb hq hV
  have htest := real_square_cutoff_difference_weak_gradient eta u g hu hg R0 r hr he hs hw i h hh
  have hvc : HasCompactSupport (realSquareCutoff eta (realDifferenceQuotient i h u)) := by
    convert (hc.mul_right (f' := eta)).mul_right (f' := realDifferenceQuotient i h u) using 1
    first | rfl | (funext x; simp only [realSquareCutoff,pow_two,Pi.mul_apply])
  have houter := real_compact_weak_test_difference_energy _ _ _ _ htest.1 hvc htest.2.1
    htest.2.2.2.2 henergy.2 i (-h)
  exact ⟨henergy.1,houter.1,henergy.2,houter.2⟩

end
end Yau

end OAI
