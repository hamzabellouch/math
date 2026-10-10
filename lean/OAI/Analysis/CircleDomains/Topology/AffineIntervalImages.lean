import OAI.Analysis.CircleDomains.Topology.AffinePathTime
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Open-piece images under the affine parameter map, including clipping
of a test interval that crosses either endpoint of the piece. -/

open Set

noncomputable section

namespace CircleDomainRigidity

theorem rescalePathTime_mem_Ioo {a b : PathTime} (hab : a < b) {t : PathTime}
    (ht : t ∈ Ioo a b) : rescalePathTime a b t ∈ Ioo (⊥ : PathTime) ⊤ := by
  have hf := affinePathTime_strictMono hab
  have he := affine_rescalePathTime hab ⟨ht.1.le, ht.2.le⟩
  constructor
  · apply hf.lt_iff_lt.mp
    rw [affinePathTime_zero, he]
    exact ht.1
  · apply hf.lt_iff_lt.mp
    rw [affinePathTime_one, he]
    exact ht.2

theorem affinePathTime_mem_Ioo {a b : PathTime} (hab : a < b) {t : PathTime}
    (ht : t ∈ Ioo (⊥ : PathTime) ⊤) : affinePathTime a b t ∈ Ioo a b := by
  change a < affinePathTime a b t ∧ affinePathTime a b t < b
  simpa only [affinePathTime_zero, affinePathTime_one] using
    And.intro (affinePathTime_strictMono hab ht.1) (affinePathTime_strictMono hab ht.2)

theorem affine_image_rescaled_Ioo {a b : PathTime} (hab : a < b) (c d : PathTime) :
    affinePathTime a b '' Ioo (rescalePathTime a b c) (rescalePathTime a b d) =
      Ioo a b ∩ Ioo c d := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hti : t ∈ Ioo (⊥ : PathTime) ⊤ :=
      ⟨lt_of_le_of_lt bot_le ht.1, lt_of_lt_of_le ht.2 le_top⟩
    exact ⟨affinePathTime_mem_Ioo hab hti,
      (rescalePathTime_lt_iff hab c t hti).mp ht.1,
      (lt_rescalePathTime_iff hab d t hti).mp ht.2⟩
  · rintro ⟨hx, htest⟩
    have hti := rescalePathTime_mem_Ioo hab hx
    have he := affine_rescalePathTime hab ⟨hx.1.le, hx.2.le⟩
    refine ⟨rescalePathTime a b x, ?_, he⟩
    constructor
    · apply (rescalePathTime_lt_iff hab c _ hti).mpr
      rw [he]
      exact htest.1
    · apply (lt_rescalePathTime_iff hab d _ hti).mpr
      rw [he]
      exact htest.2

end CircleDomainRigidity

end

end OAI
