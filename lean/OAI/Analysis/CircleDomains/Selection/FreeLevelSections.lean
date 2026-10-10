import OAI.Analysis.CircleDomains.Modulus.TupleIncidence
import OAI.Analysis.CircleDomains.Probability.CircleNullImage

namespace OAI

/-! Unique level traces away from the countable flags provide the null
circle sections required by the whole-image atomless test. -/

open Set MeasureTheory Filter

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

theorem unitAddCircle_volume_singleton (t : UnitAddCircle) : volume ({t} : Set UnitAddCircle) = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
  simpa only [Set.image_singleton] using
    (volume_addCircle_image_eq_zero (show volume ({x} : Set ℝ) = 0 from measure_singleton x))

theorem level_section_null_of_unique (H : ℕ → Set (UnitAddCircle × X)) (x : X)
    (hunique : ∀ i t u, (t, x) ∈ H i → (u, x) ∈ H i → t = u) (i : ℕ) :
    volume {t : UnitAddCircle | (t, x) ∈ H i} = 0 := by
  have hs : ({t : UnitAddCircle | (t, x) ∈ H i}).Subsingleton := by
    intro t ht u hu
    exact hunique i t u ht hu
  let : NullSingletonClass (volume : Measure UnitAddCircle) :=
    ⟨unitAddCircle_volume_singleton⟩
  exact hs.countable.measure_zero volume

variable [MeasurableSpace X]

theorem ae_free_level_sections (H : ℕ → Set (UnitAddCircle × X)) (B flags : Set X)
    (ν : Measure X) [NullSingletonClass ν] (hflags : flags.Countable) (hB : ν Bᶜ = 0)
    (hunique : ∀ x ∈ B \ flags, ∀ i t u, (t, x) ∈ H i → (u, x) ∈ H i → t = u) :
    ∀ᵐ x ∂ν, x ∈ B ∧ ∀ i, volume {t : UnitAddCircle | (t, x) ∈ H i} = 0 := by
  have hmem : ∀ᵐ x ∂ν, x ∈ B := by
    rw [ae_iff]
    change ν Bᶜ = 0
    exact hB
  have hnot : ∀ᵐ x ∂ν, x ∉ flags :=
    (measure_eq_zero_iff_ae_notMem).mp (hflags.measure_zero ν)
  filter_upwards [hmem, hnot] with x hx hxflags
  exact ⟨hx, level_section_null_of_unique H x (hunique x ⟨hx, hxflags⟩)⟩

end CircleDomainRigidity

end

end OAI
