import OAI.Geometry.NodalSets.Elliptic.RealLocalWeakCutoff
import OAI.Geometry.NodalSets.Elliptic.RealWeakDifferenceBound

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_weak_cutoff_difference_bound {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u g eta : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K)) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ K) (i : Fin n)
    (hweak : ∀ phi : Coord n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ K →
      (∫ x in K, u x*coordPartial phi x i)=-(∫ x in K, g x*phi x)) (h : ℝ) :
    MemLp (realDifferenceQuotient i h (fun x ↦ eta x*u x)) 2 volume ∧
      (∫ x, (realDifferenceQuotient i h (fun y ↦ eta y*u y) x)^2) ≤
        ∫ x, (eta x*g x+coordPartial eta x i*u x)^2 := by
  have hloc := real_local_weak_cutoff hK u g eta hu hg he hs i hweak
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hv : Integrable (fun x ↦ eta x*u x) := by
    apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp
    · exact (hloc.1.mono_measure Measure.restrict_le_self).integrable (by norm_num)
    · intro x hx
      exact hs (subset_tsupport eta (by
        intro hz
        exact hx (by simp only [hz,zero_mul])))
  exact real_weak_derivative_difference_bound _ _ hv hloc.1 hloc.2.1 i
    (fun psi hp hc ↦ (hloc.2.2 psi hp hc).2.2) h

end
end Yau

end OAI
