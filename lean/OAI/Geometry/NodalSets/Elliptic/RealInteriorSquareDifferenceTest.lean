import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas
import OAI.Geometry.NodalSets.Elliptic.RealSquareDifferenceTest

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_interior_square_difference_test {n : ℕ} (R r : ℝ) (hr : r ≤ R)
    (C : Coord n → Fin n → Fin n → ℝ) (hC : ∀ a j, Continuous (fun x ↦ C x a j))
    (u : Coord n → ℝ) (V0 P0 G0 : Fin n → Coord n → ℝ) (F0 : Coord n → ℝ)
    (hu : MemLp u 2 (volume.restrict (realCenteredCube n R)))
    (hV : ∀ a, MemLp (V0 a) 2 (volume.restrict (realCenteredCube n R)))
    (hP : ∀ a, MemLp (P0 a) 2 (volume.restrict (realCenteredCube n R)))
    (hG : ∀ a, MemLp (G0 a) 2 (volume.restrict (realCenteredCube n R)))
    (hF : MemLp F0 2 (volume.restrict (realCenteredCube n R)))
    (hweak : ∀ j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ realCenteredCube n R →
      (∫ x in realCenteredCube n R, u x*coordPartial psi x j) =
        -(∫ x in realCenteredCube n R, V0 j x*psi x))
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ realCenteredCube n R →
      (∑ a, ∑ j, ∫ x in realCenteredCube n R, C x a j*P0 a x*coordPartial psi x j) =
        (∫ x in realCenteredCube n R, F0 x*psi x)-
          ∑ j, ∫ x in realCenteredCube n R, G0 j x*coordPartial psi x j)
    (eta : Coord n → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior (realCenteredCube n r))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r) :
    let Q := realCenteredCube n R
    let U := Q.indicator u
    let V := fun a ↦ Q.indicator (V0 a)
    let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, C x a j*P0 a x)
    let G := fun j ↦ Q.indicator (G0 j)
    let F := Q.indicator F0
    let v := realSquareCutoff eta (realDifferenceQuotient i h U)
    let P := realSquareCutoffGradient eta (realDifferenceQuotient i h U)
      (fun j ↦ realDifferenceQuotient i h (V j))
    MemLp v 2 volume ∧ (∀ j, MemLp (P j) 2 volume) ∧
    (∀ j, Integrable (fun x ↦ realDifferenceQuotient i h (A j) x*P j x) ∧
      Integrable (fun x ↦ realDifferenceQuotient i h (G j) x*P j x)) ∧
    Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) v x) ∧
    (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*realDifferenceQuotient i (-h) v x)-
        (∑ j, ∫ x, realDifferenceQuotient i h (G j) x*P j x) := by
  dsimp only
  let Q := realCenteredCube n R
  have hQ : IsCompact Q := realCenteredCube_isCompact n R
  let U := Q.indicator u
  let V := fun a ↦ Q.indicator (V0 a)
  let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, C x a j*P0 a x)
  let G := fun j ↦ Q.indicator (G0 j)
  let F := Q.indicator F0
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hu
  have hVG (a : Fin n) : MemLp (V a) 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr (hV a)
  have hGG (j : Fin n) : MemLp (G j) 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr (hG j)
  have hFG : MemLp F 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hF
  have hcoef (a j : Fin n) : MemLp (fun x ↦ C x a j*P0 a x) 2 (volume.restrict Q) := by
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hQ _ (hC a j)
    exact (hb _ (hP a)).1
  have hAG (j : Fin n) : MemLp (A j) 2 volume :=
    (memLp_indicator_iff_restrict hQ.measurableSet).mpr
      (memLp_finsetSum Finset.univ (fun a _ ↦ hcoef a j))
  have hzpair (a b : Coord n → ℝ) : (∫ x, Q.indicator a x*b x)=∫ x in Q, a x*b x := by
    simp only [← indicator_mul_left,integral_indicator hQ.measurableSet]
  have hW (j : Fin n) (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∫ x, U x*coordPartial psi x j)=-(∫ x, V j x*psi x) := by
    change (∫ x, Q.indicator u x*coordPartial psi x j)=-(∫ x, Q.indicator (V0 j) x*psi x)
    rw [hzpair,hzpair]
    exact hweak j psi hp hpc hps
  have hE (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∑ j, ∫ x, A j x*coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*coordPartial psi x j) := by
    have hi (a j : Fin n) : IntegrableOn (fun x ↦ C x a j*P0 a x*coordPartial psi x j) Q :=
      (hcoef a j).integrable_mul (real_continuous_memLp_compact hQ _ (real_coordPartial_smooth psi hp j).continuous)
    have hsum (j : Fin n) : (∫ x, A j x*coordPartial psi x j) =
        ∑ a, ∫ x in Q, C x a j*P0 a x*coordPartial psi x j := by
      change (∫ x, Q.indicator (fun y ↦ ∑ a, C y a j*P0 a y) x*coordPartial psi x j)=_
      rw [hzpair]
      simp only [Finset.sum_mul]
      exact integral_finsetSum Finset.univ (fun a _ ↦ hi a j)
    simp only [hsum]
    rw [Finset.sum_comm]
    change (∑ a, ∑ j, ∫ x in Q, C x a j*P0 a x*coordPartial psi x j) =
      (∫ x, Q.indicator F0 x*psi x)-(∑ j, ∫ x, Q.indicator (G0 j) x*coordPartial psi x j)
    simp only [hzpair]
    exact heq psi hp hpc hps
  exact real_square_cutoff_difference_test A G F hAG hGG hFG R r hr hE U V hU hVG hW eta he hc hs i h hh

end
end Yau

end OAI
