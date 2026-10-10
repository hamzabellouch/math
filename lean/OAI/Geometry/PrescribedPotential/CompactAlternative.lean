import Mathlib

namespace OAI

/-! Compact Alternative. -/

section

 
noncomputable section
namespace GlobalElliptic
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

lemma compact_one_sub_surjective (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hker : ∀ u : H, T u = u → u = 0) :
    Function.Surjective (1 - T : H →L[ℝ] H) := by
  have hn : ¬ Module.End.HasEigenvalue (T : Module.End ℝ H) 1 := by
    intro hev
    obtain ⟨u, hu⟩ := hev.exists_hasEigenvector
    apply hu.2
    apply hker u
    have heq : T u = (1 : ℝ) • u := Module.End.HasEigenvector.apply_eq_smul hu
    exact heq.trans (one_smul ℝ u)
  have hr := (hT.hasEigenvalue_or_mem_resolventSet (by norm_num : (1 : ℝ) ≠ 0)).resolve_left hn
  rw [spectrum.mem_resolventSet_iff] at hr
  have hu : IsUnit (1 - T : H →L[ℝ] H) := by simpa only [map_one] using hr
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2

end GlobalElliptic

end
end

end OAI
