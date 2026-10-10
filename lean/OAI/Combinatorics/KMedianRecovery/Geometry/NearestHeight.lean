import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.Nearest
import OAI.Combinatorics.KMedianRecovery.Recovery.Height

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalHeight RationalOpenability
lemma nearest_height {m d a : ℕ} (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,Height (distance f j) a) (W : Finset (Fin m)) (j : Fin d) :
    Height (nearest distance W j) a := by
  unfold nearest
  split_ifs with hW
  · obtain ⟨f,hf,he⟩ := Finset.exists_mem_eq_inf' hW (fun f => distance f j)
    rw [he]
    exact hd f j
  · exact RationalHeight.zero _
end MetricKMedianRecovery.EffectiveOpenability

end OAI
