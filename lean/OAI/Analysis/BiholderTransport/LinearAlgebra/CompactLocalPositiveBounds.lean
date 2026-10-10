import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ContDiffParametricQuadratic

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma compact_local_positive_bounds {A : Type*} [TopologicalSpace A]
    {K : Set A} (hK : IsCompact K) {P : ℝ → ℝ → A → Prop}
    (hmono : ∀ {r R b B : ℝ}, 0<r → r≤R → b≤B → ∀ a, P R b a → P r B a)
    (hlocal : ∀ a∈K, ∃ r b : ℝ, 0<r ∧ 0<b ∧ ∀ᶠ z in 𝓝 a, P r b z) :
    ∃ r b : ℝ, 0<r ∧ 0<b ∧ ∀ a∈K, P r b a := by
  obtain ⟨r,hr,b,hb,H⟩ := compact_eventually_uniform_radius_bound
    (T := Unit) (t := ()) (P := fun r b (_ : Unit) a => P r b a) hK
    (fun hr hR hB _ a ha => hmono hr hR hB a ha) (by
      intro a ha
      obtain ⟨r,b,hr,hb,H⟩ := hlocal a ha
      exact ⟨r,hr,b,hb,continuousAt_snd.eventually H⟩)
  exact ⟨r,b,hr,hb,H.self_of_nhds⟩

end WeakMTWTransport

end

end

end

end OAI
