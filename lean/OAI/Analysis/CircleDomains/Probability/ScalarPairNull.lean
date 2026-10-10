import OAI.Analysis.CircleDomains.Probability.CircleNullImage
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! Passing prescribed real scalar trace pairs to their unit-circle levels
preserves planar outer-nullity. No measurability of the trace image is needed. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 def scalarPairModOne (p : ℝ × ℝ) : UnitAddCircle × UnitAddCircle :=
  (p.1, p.2)

 theorem volume_scalarPairModOne_image_eq_zero {A : Set (ℝ × ℝ)}
    (hA : volume A = 0) :
    ((volume : Measure UnitAddCircle).prod volume) (scalarPairModOne '' A) = 0 := by
  have hpiece (a b : ℝ) :
      ((volume : Measure UnitAddCircle).prod volume)
        (scalarPairModOne '' (A ∩ (Ioc a (a + 1) ×ˢ Ioc b (b + 1)))) = 0 := by
    let e₁ := AddCircle.measurableEquivIoc (1 : ℝ) a
    let e₂ := AddCircle.measurableEquivIoc (1 : ℝ) b
    let e := e₁.prodCongr e₂
    let g : (Ioc a (a + 1)) × (Ioc b (b + 1)) → ℝ × ℝ :=
      Prod.map Subtype.val Subtype.val
    have he₁ : MeasurePreserving e₁ volume (volume.comap Subtype.val) :=
      AddCircle.measurePreserving_equivIoc (1 : ℝ)
    have he₂ : MeasurePreserving e₂ volume (volume.comap Subtype.val) :=
      AddCircle.measurePreserving_equivIoc (1 : ℝ)
    let : SFinite (volume.comap (Subtype.val : Ioc a (a + 1) → ℝ)) := he₁.sfinite
    let : SFinite (volume.comap (Subtype.val : Ioc b (b + 1) → ℝ)) := he₂.sfinite
    have he : MeasurePreserving e (volume.prod volume)
        ((volume.comap (Subtype.val : Ioc a (a + 1) → ℝ)).prod
          (volume.comap (Subtype.val : Ioc b (b + 1) → ℝ))) := he₁.prod he₂
    have hg₁ : MeasurePreserving (Subtype.val : Ioc a (a + 1) → ℝ)
        (volume.comap Subtype.val) (volume.restrict (Ioc a (a + 1))) :=
      ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Ioc volume⟩
    have hg₂ : MeasurePreserving (Subtype.val : Ioc b (b + 1) → ℝ)
        (volume.comap Subtype.val) (volume.restrict (Ioc b (b + 1))) :=
      ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Ioc volume⟩
    have hg : MeasurePreserving g
        ((volume.comap (Subtype.val : Ioc a (a + 1) → ℝ)).prod
          (volume.comap (Subtype.val : Ioc b (b + 1) → ℝ)))
        ((volume.restrict (Ioc a (a + 1))).prod (volume.restrict (Ioc b (b + 1)))) :=
      hg₁.prod hg₂
    have hnull : ((volume.restrict (Ioc a (a + 1))).prod
        (volume.restrict (Ioc b (b + 1)))) A = 0 := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact le_antisymm (hA ▸ Measure.restrict_apply_le _ _) bot_le
    have hset : (g ∘ e) ⁻¹' A =
        scalarPairModOne '' (A ∩ (Ioc a (a + 1) ×ˢ Ioc b (b + 1))) := by
      ext y
      constructor
      · intro hy
        refine ⟨g (e y), ⟨hy, (e₁ y.1).property, (e₂ y.2).property⟩, ?_⟩
        exact Prod.ext AddCircle.coe_equivIoc AddCircle.coe_equivIoc
      · rintro ⟨x, ⟨hx, hx₁, hx₂⟩, rfl⟩
        change ((AddCircle.equivIoc (1 : ℝ) a (x.1 : UnitAddCircle)).val,
          (AddCircle.equivIoc (1 : ℝ) b (x.2 : UnitAddCircle)).val) ∈ A
        rw [AddCircle.equivIoc_coe_eq hx₁, AddCircle.equivIoc_coe_eq hx₂]
        exact hx
    rw [← hset]
    exact (hg.comp he).preimage_null hnull
  have hcover : scalarPairModOne '' A ⊆ ⋃ k : ℤ × ℤ,
      scalarPairModOne '' (A ∩
        (Ioc ((k.1 : ℝ) - 1) ((k.1 : ℝ) - 1 + 1) ×ˢ
          Ioc ((k.2 : ℝ) - 1) ((k.2 : ℝ) - 1 + 1))) := by
    rintro y ⟨x, hx, rfl⟩
    refine mem_iUnion.mpr ⟨(⌈x.1⌉, ⌈x.2⌉), x, ⟨hx, ?_, ?_⟩, rfl⟩
    · constructor <;> linarith [Int.ceil_lt_add_one x.1, Int.le_ceil x.1]
    · constructor <;> linarith [Int.ceil_lt_add_one x.2, Int.le_ceil x.2]
  exact measure_mono_null hcover (measure_iUnion_null fun k => hpiece _ _)

 theorem scalar_trace_pair_null_mod_one {X : Type*} (B : Set X) (u v : X → ℝ)
    (h : volume ((fun x => (u x, v x)) '' B) = 0) :
    ((volume : Measure UnitAddCircle).prod volume)
      ((fun x => ((u x : UnitAddCircle), (v x : UnitAddCircle))) '' B) = 0 := by
  simpa only [image_image, comp_def, scalarPairModOne] using
    volume_scalarPairModOne_image_eq_zero h

end CircleDomainRigidity

end

end OAI
