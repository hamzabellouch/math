import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalRepresentativeGluing

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

theorem physical_region_glue {ι : Type*} [Countable ι]
    (O : ι → Set Coord3) (hO : ∀ i,IsOpen (O i))
    {U : Set Coord3} (hUm : MeasurableSet U) (hOU : ∀ i,O i⊆U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball)
    (hcover : ∀ᵐ y : Coord3,y∈U → y∈⋃ i,O i)
    (w : Fin 2 → H1) (g : ι → Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hreg : ∀ i,∀ᵐ y : Coord3,y∈O i → y∈regularRegion (g i) A (O i))
    (he : ∀ i,(fun y j => weakValue (w j) (WithLp.toLp 2 y))=ᵐ[volume.restrict (O i)] g i) :
    ∃ v : Coord3 → Fin 2 → ℝ,
      (∀ᵐ y : Coord3,y∈U → v y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,∀ j : Fin 2,
        fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i) ∧
      volume (U \ regularRegion v A U)=0 := by
  let I := Σ i : ι,{V : Set Coord3 // V⊆O i ∧ RegularPatch (g i) A V}
  let V : I → Set Coord3 := fun i => i.2.val
  let f : I → Coord3 → Fin 2 → ℝ := fun i => g i.1
  have hV : ∀ i,IsOpen (V i) := fun i => i.2.property.2.1
  have hVU : ∀ i,V i⊆U := fun i => i.2.property.1.trans (hOU i.1)
  have hVR : ∀ i,RegularPatch (f i) A (V i) := fun i => i.2.property.2
  have hc : ∀ᵐ y : Coord3,y∈U → y∈⋃ i,V i := by
    filter_upwards [hcover,ae_all_iff.mpr hreg] with y hc hr hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hc hy)
    obtain ⟨W,hWO,hW,hyW⟩ := mem_regularRegion_iff.mp (hr i hi)
    exact mem_iUnion.mpr ⟨⟨i,⟨W,hWO,hW⟩⟩,hyW⟩
  have he' : ∀ i,(fun y j => weakValue (w j) (WithLp.toLp 2 y))=ᵐ[volume.restrict (V i)] f i := by
    intro index
    apply (ae_restrict_iff' (hV index).measurableSet).mpr
    filter_upwards [(ae_restrict_iff' (hO index.1).measurableSet).mp (he index.1)] with point equality membership
    exact equality (index.2.property.1 membership)
  exact physical_representative_glue V hV hUm hVU hUb hc w f A hVR he'

end ScalarConductivity

end
end

end OAI
