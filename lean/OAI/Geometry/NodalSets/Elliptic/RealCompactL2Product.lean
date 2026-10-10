import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas
import OAI.Geometry.NodalSets.Elliptic.RealL2ZeroExtension

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_compact_localL2_product {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta u : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K)
    (hu : MemLp u 2 (volume.restrict K)) : MemLp (fun x ↦ eta x*u x) 2 volume := by
  obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hK eta he
  have hlocal := (hb u hu).1
  have hglobal := (memLp_indicator_iff_restrict hK.measurableSet).mpr hlocal
  have heq : K.indicator (fun x ↦ eta x*u x) = fun x ↦ eta x*u x := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)),zero_mul]
  rwa [heq] at hglobal

end
end Yau

end OAI
