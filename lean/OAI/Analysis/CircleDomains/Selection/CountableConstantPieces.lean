import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

/-! Measurability of a function that is constant on countably many
closed pieces and continuous on their complement. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

 theorem measurable_of_countable_constant_pieces
    {X Y ι : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [Countable ι]
    (K : ι → Set X) (hK : ∀ j, IsClosed (K j)) (b : X → Y)
    (v : ι → Y) (hv : ∀ j x, x ∈ K j → b x = v j)
    (hc : ContinuousOn b (⋃ j, K j)ᶜ) : Measurable b := by
  classical
  let S := ⋃ j, K j
  have hS : MeasurableSet S := MeasurableSet.iUnion (fun j => (hK j).measurableSet)
  have hbc : Measurable (Sᶜ.domRestrict b) :=
    (continuousOn_iff_continuous_domRestrict.mp hc).measurable
  intro U hU
  have hleft : MeasurableSet (b ⁻¹' U ∩ Sᶜ) := by
    convert hS.compl.subtype_image (hbc hU) using 1
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_image,domRestrict_apply]
    exact ⟨fun h => ⟨⟨x,h.2⟩,h.1,rfl⟩,fun ⟨p,hp,hpx⟩ => hpx ▸ ⟨hp,p.property⟩⟩
  have he : b ⁻¹' U = (b ⁻¹' U ∩ Sᶜ) ∪ ⋃ j, if v j ∈ U then K j else ∅ := by
    ext x
    constructor
    · intro hx
      by_cases hs : x ∈ S
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hs
        have hu : v j ∈ U := by rw [← hv j x hj]; exact hx
        exact Or.inr (mem_iUnion.mpr ⟨j,by rw [ite_eq_left hu]; exact hj⟩)
      · exact Or.inl ⟨hx,hs⟩
    · rintro (hx | hx)
      · exact hx.1
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
        split_ifs at hj with hu
        · change b x ∈ U
          rwa [hv j x hj]
        · exact hj.elim
  rw [he]
  apply hleft.union
  apply MeasurableSet.iUnion
  intro j
  split_ifs
  · exact (hK j).measurableSet
  · exact MeasurableSet.empty

end CircleDomainRigidity

end

end OAI
