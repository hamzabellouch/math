import OAI.Geometry.NodalSets.Elliptic.RealH1DifferenceEquation
import OAI.Geometry.NodalSets.Elliptic.RealSquareCutoffWeakGradient

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_square_cutoff_difference_test {n : ℕ}
    (A G : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (hA : ∀ j, MemLp (A j) 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hF : MemLp F 2 volume) (R r : ℝ) (hr : r ≤ R)
    (heq : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∑ j, ∫ x, A j x*coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*coordPartial psi x j))
    (u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g j x*psi x))
    (eta : Coord n → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior (realCenteredCube n r))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r) :
    let v := realSquareCutoff eta (realDifferenceQuotient i h u)
    let P := realSquareCutoffGradient eta (realDifferenceQuotient i h u)
      (fun j ↦ realDifferenceQuotient i h (g j))
    MemLp v 2 volume ∧ (∀ j, MemLp (P j) 2 volume) ∧
    (∀ j, Integrable (fun x ↦ realDifferenceQuotient i h (A j) x*P j x) ∧
      Integrable (fun x ↦ realDifferenceQuotient i h (G j) x*P j x)) ∧
    Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) v x) ∧
    (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*realDifferenceQuotient i (-h) v x)-
        (∑ j, ∫ x, realDifferenceQuotient i h (G j) x*P j x) := by
  dsimp only
  have htest := real_square_cutoff_difference_weak_gradient eta u g hu hg R r hr he
    (hs.trans interior_subset) hw i h hh
  refine ⟨htest.1,htest.2.1,?_⟩
  exact real_divergence_H1_difference_equation A G F hA hG hF R r hr heq i h hh
    hc hs _ _ htest.1 htest.2.1 htest.2.2.1 htest.2.2.2.1 htest.2.2.2.2

end
end Yau

end OAI
