import Mathlib.GroupTheory.Finiteness
import Mathlib.Logic.Equiv.List

namespace OAI

/-! # Countability from a finite group generating set -/

namespace PolycyclicRecognition

theorem countable_of_group_fg (G : Type) [Group G] [Group.FG G] : Countable G := by
  obtain ⟨α, hα, f, hf⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp
    (inferInstance : Group.FG G)
  let := hα
  have : Countable (FreeGroup α) := by
    unfold FreeGroup
    infer_instance
  exact hf.countable

end PolycyclicRecognition

end OAI
