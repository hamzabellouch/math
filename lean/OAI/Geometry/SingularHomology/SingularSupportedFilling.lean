import OAI.Geometry.SingularHomology.SingularChainInclusion
import OAI.Geometry.SingularHomology.SingularCycleFilling

namespace OAI

noncomputable section

namespace Problem340

theorem exists_realSingularChain_filling_in_range
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace X]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f) (n : ℕ)
    (z : (realSingularChainComplex Y).X (n + 1))
    (hz : ((realSingularChainComplex Y).d (n + 1) n).hom z = 0)
    (hs : z ∈ LinearMap.range ((realSingularChainMap f hf).f (n + 1)).hom) :
    ∃ b : (realSingularChainComplex Y).X (n + 2),
      b ∈ LinearMap.range ((realSingularChainMap f hf).f (n + 2)).hom ∧
      ((realSingularChainComplex Y).d (n + 2) (n + 1)).hom b = z := by
  obtain ⟨w, hw, hwz⟩ :=
    realSingularChainMap_exists_cycle_lift f hf hinj (n + 1) n z hz hs
  obtain ⟨b, hb⟩ := exists_realSingularChain_filling_of_contractible X n w hw
  refine ⟨((realSingularChainMap f hf).f (n + 2)).hom b, ⟨b, rfl⟩, ?_⟩
  rw [realSingularChainMap_d, hb, hwz]

theorem exists_realSingularChain_filling_in_subset
    {X : Type} [TopologicalSpace X] (s : Set X) [ContractibleSpace s] (n : ℕ)
    (z : (realSingularChainComplex X).X (n + 1))
    (hz : ((realSingularChainComplex X).d (n + 1) n).hom z = 0)
    (hs : z ∈ LinearMap.range
      ((realSingularChainMap (Subtype.val : s → X) continuous_subtype_val).f (n + 1)).hom) :
    ∃ b : (realSingularChainComplex X).X (n + 2),
      b ∈ LinearMap.range
        ((realSingularChainMap (Subtype.val : s → X) continuous_subtype_val).f (n + 2)).hom ∧
      ((realSingularChainComplex X).d (n + 2) (n + 1)).hom b = z :=
  exists_realSingularChain_filling_in_range Subtype.val continuous_subtype_val
    Subtype.val_injective n z hz hs

end Problem340

end

end OAI
