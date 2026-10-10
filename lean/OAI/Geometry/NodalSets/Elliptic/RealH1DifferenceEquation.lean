import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas
import OAI.Geometry.NodalSets.Elliptic.RealH1TestExtension

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_divergence_H1_difference_equation {n : ℕ}
    (A G : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (hA : ∀ j, MemLp (A j) 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hF : MemLp F 2 volume) (R r : ℝ) (hr : r ≤ R)
    (heq : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∑ j, ∫ x, A j x*coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*coordPartial psi x j))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r) {K : Set (Coord n)}
    (hK : IsCompact K) (hKr : K ⊆ interior (realCenteredCube n r))
    (v : Coord n → ℝ) (P : Fin n → Coord n → ℝ)
    (hv : MemLp v 2 volume) (hP : ∀ j, MemLp (P j) 2 volume)
    (hsv : ∀ x, x ∉ K → v x=0) (hsP : ∀ j x, x ∉ K → P j x=0)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, v x*coordPartial psi x j)=-(∫ x, P j x*psi x)) :
    (∀ j, Integrable (fun x ↦ realDifferenceQuotient i h (A j) x*P j x) ∧
      Integrable (fun x ↦ realDifferenceQuotient i h (G j) x*P j x)) ∧
    Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) v x) ∧
    (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*realDifferenceQuotient i (-h) v x)-
        (∑ j, ∫ x, realDifferenceQuotient i h (G j) x*P j x) := by
  obtain ⟨w,hwS,hwC,hwK,ht,hdt⟩ := real_compact_weak_H1_smooth_approximation
    hK (realCenteredCube_isCompact n r) hKr v P hv hP hsv hsP hw
  have hDA (j : Fin n) := realDifferenceQuotient_memLp i h (A j) (hA j)
  have hDG (j : Fin n) := realDifferenceQuotient_memLp i h (G j) (hG j)
  have hDF := realDifferenceQuotient_memLp i h F hF
  have hwLp (m : ℕ) := real_compact_continuous_memLp (w m) (hwS m).continuous (hwC m)
  have hdLp (j : Fin n) (m : ℕ) := real_compact_continuous_memLp _
    (real_coordPartial_smooth (w m) (hwS m) j).continuous ((hwC m).fderiv_apply ℝ (Pi.single j 1))
  have hleft := tendsto_finsetSum Finset.univ (fun j _ ↦ real_L2_strong_pairing_tendsto
    _ (P j) (hDA j) (hP j) (fun m x ↦ coordPartial (w m) x j) (hdLp j) (hdt j))
  have hdiv := tendsto_finsetSum Finset.univ (fun j _ ↦ real_L2_strong_pairing_tendsto
    _ (P j) (hDG j) (hP j) (fun m x ↦ coordPartial (w m) x j) (hdLp j) (hdt j))
  have hscalar := real_L2_strong_pairing_tendsto _ v hDF hv w hwLp ht
  have he (m : ℕ) := (real_divergence_forcing_difference_equation A G F hA hG hF R r hr heq
    i h hh (w m) (hwS m) (hwC m) (hwK m)).2.2
  have hsame (m : ℕ) : (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*coordPartial (w m) x j) =
      (∫ x, realDifferenceQuotient i h F x*w m x)-
        ∑ j, ∫ x, realDifferenceQuotient i h (G j) x*coordPartial (w m) x j := by
    rw [(real_differenceQuotient_pairing i h F (w m) hF (hwLp m)).2.2]
    exact he m
  have hlim := tendsto_nhds_unique hleft ((hscalar.sub hdiv).congr (fun m ↦ (hsame m).symm))
  refine ⟨fun j ↦ ⟨(hDA j).integrable_mul (hP j),(hDG j).integrable_mul (hP j)⟩,
    hF.integrable_mul (realDifferenceQuotient_memLp i (-h) v hv),?_⟩
  rw [(real_differenceQuotient_pairing i h F v hF hv).2.2] at hlim
  exact hlim

end
end Yau

end OAI
