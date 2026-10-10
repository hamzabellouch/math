import OAI.Analysis.CircleDomains.Selection.AffineResidualExposure

namespace OAI

/-! Affine restriction preserves the atomless residual-image condition.
The two new endpoints are included explicitly among the countable additions. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem affine_exposed_full_image_countable (B : Set X) {a b : PathTime}
    (hab : a < b) (Γ : TaggedPath X) :
    (affineRestrictedPath a b Γ.1 ''
      (residualTimes B (affineRestrictedTaggedPath a b Γ) \
        (affinePathTime a b ⁻¹' residualTimes B Γ))).Countable := by
  have hc := (affine_exposed_image_countable B hab Γ).union
    (toFinite ({affineRestrictedPath a b Γ.1 ⊥, affineRestrictedPath a b Γ.1 ⊤} : Set X)).countable
  apply hc.mono
  rintro x ⟨t, ⟨ht, hold⟩, rfl⟩
  by_cases hzero : t = ⊥
  · right
    simp [hzero]
  by_cases hone : t = ⊤
  · right
    simp [hone]
  left
  exact ⟨t, ⟨⟨ht, bot_lt_iff_ne_bot.mpr hzero, lt_top_iff_ne_top.mpr hone⟩, hold⟩, rfl⟩

theorem residualImage_affine_null [MeasurableSpace X] [MeasurableSingletonClass X]
    (B : Set X) {a b : PathTime} (hab : a < b) (Γ : TaggedPath X)
    (ν : Measure X) [NullSingletonClass ν] (hnull : ν (residualImage B Γ) = 0) :
    ν (residualImage B (affineRestrictedTaggedPath a b Γ)) = 0 := by
  have hsub : residualImage B (affineRestrictedTaggedPath a b Γ) ⊆
      residualImage B Γ ∪ affineRestrictedPath a b Γ.1 ''
        (residualTimes B (affineRestrictedTaggedPath a b Γ) \
          (affinePathTime a b ⁻¹' residualTimes B Γ)) := by
    rintro x ⟨t, ht, rfl⟩
    by_cases hold : affinePathTime a b t ∈ residualTimes B Γ
    · exact Or.inl ⟨affinePathTime a b t, hold, rfl⟩
    · exact Or.inr ⟨t, ⟨ht, hold⟩, rfl⟩
  exact measure_mono_null hsub (measure_union_null hnull
    ((affine_exposed_full_image_countable B hab Γ).measure_zero ν))

end CircleDomainRigidity

end

end OAI
