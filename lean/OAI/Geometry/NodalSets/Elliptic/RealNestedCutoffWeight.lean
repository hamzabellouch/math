import OAI.Geometry.NodalSets.Elliptic.RealCutoffIntegralsLemmas

namespace OAI

namespace Yau.Geometry
open MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_nested_cutoff_support (eta chi : Yau.Jets.Coord → ℝ)
    (h : ∀ x ∈ tsupport eta, chi x=1) : tsupport eta ⊆ tsupport chi := by
  intro x hx
  apply subset_tsupport chi
  change chi x≠0
  rw [h x hx]
  exact one_ne_zero

lemma real_nested_cutoff_weight (eta chi : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (h : ∀ x ∈ tsupport eta, chi x=1) :
    ∃ D > 0, ∀ x, realCutoffWeight eta x ≤ D*chi x^2 := by
  obtain ⟨A,hA⟩ := hc.isCompact.exists_bound_of_continuousOn (realCutoffWeight_smooth eta heta).continuous.continuousOn
  refine ⟨|A|+1,by positivity,?_⟩
  intro x
  by_cases hx : x ∈ tsupport eta
  · have hb := (le_abs_self (realCutoffWeight eta x)).trans (by simpa only [Real.norm_eq_abs] using hA x hx)
    rw [h x hx,one_pow,mul_one]
    exact hb.trans ((le_abs_self A).trans (by linarith))
  · rw [realCutoffWeight_zero_off_support eta hx]
    positivity

end
end Yau.Geometry

end OAI
