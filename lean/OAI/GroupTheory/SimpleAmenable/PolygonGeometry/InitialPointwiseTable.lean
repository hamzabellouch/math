import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FinitelyManyTranslationRelations
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GenuineFiniteGeneration
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CanonicalSectors
import OAI.GroupTheory.SimpleAmenable.Configurations.PointwisePolygonTables

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceInitialPointwiseTable

variable {a m : ℕ} {ι : Type*} [Finite ι]

noncomputable def actualPolygonTableHom (U : ι → polygonAlgebra a) :
    (Set.range (polygonAssignment U) → alternatingGroup (Fin m)) →*
      polygonAlternatingGroup a m := by
  classical
  let := Fintype.ofFinite (Set.range (polygonAssignment U))
  exact (actualPolygonLabelling U).tableHom

@[simp] theorem actualPolygonTableHom_apply (U : ι → polygonAlgebra a)
    (σ : Set.range (polygonAssignment U) → alternatingGroup (Fin m))
    (p : TrackPoint a m) :
    (actualPolygonTableHom U σ).val.val p =
      ((σ ⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩).val p.1,p.2) := by
  classical
  let := Fintype.ofFinite (Set.range (polygonAssignment U))
  exact (actualPolygonLabelling U).tableHom_apply σ p

theorem actualPolygonTableHom_injective (U : ι → polygonAlgebra a) :
    Function.Injective (actualPolygonTableHom (m := m) U) := by
  classical
  let := Fintype.ofFinite (Set.range (polygonAssignment U))
  exact (actualPolygonLabelling U).tableHom_injective (actualPolygonLabelling_surjective U)

noncomputable def polygonTableInput (U : ι → polygonAlgebra a) (i : ι) :
    alternatingGroup (Fin m) →* (Set.range (polygonAssignment U) → alternatingGroup (Fin m)) :=
  sectorMask {ω | ω.val i = true}

@[simp] theorem actualPolygonTableHom_input (U : ι → polygonAlgebra a) (i : ι)
    (σ : alternatingGroup (Fin m)) :
    actualPolygonTableHom U (polygonTableInput U i σ) = conditionalAlternatingHom (U i) σ := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [actualPolygonTableHom_apply]
  change ((polygonTableInput U i σ ⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩).val p.1,p.2) =
    conditionalPerm (U i) σ.val p
  rw [conditionalPerm_apply]
  by_cases hp : p.2 ∈ (U i).val
  · have hω : (⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩ :
        Set.range (polygonAssignment U)) ∈ {ω | ω.val i = true} := by
      change decide (p.2 ∈ (U i).val) = true
      exact decide_eq_true hp
    rw [polygonTableInput, sectorMask_of_mem _ _ _ hω, ite_eq_left hp]
  · have hω : (⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩ :
        Set.range (polygonAssignment U)) ∉ {ω | ω.val i = true} := by
      change ¬decide (p.2 ∈ (U i).val) = true
      simpa only [decide_eq_true_eq] using hp
    rw [polygonTableInput, sectorMask_of_not_mem _ _ _ hω, ite_eq_right hp]
    rfl

def sourceConditionalLabel (m : ℕ)
    (b : Fin 5 × {σ : Equiv.Perm (Fin (m+1)) //
      σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}) :
    SourceGeneratorLabel m := Sum.inl b

theorem source_initial_table_lifts_eventually (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1) (hm' : 2 ≤ m) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ ρ : (Set.range (polygonAssignment (initialTest a r)) →
          alternatingGroup (Fin (m+1))) →*
          BoundedRelationCover M (alternatingGenerator a r m hm'),
        (coverMap M (alternatingGenerator a r m hm')).comp ρ =
          actualPolygonTableHom (initialTest a r) ∧
        Function.Injective ρ ∧
        ∀ b, ρ (polygonTableInput (initialTest a r) b.1
            (⟨b.2.val,b.2.property.1⟩ : alternatingGroup (Fin (m+1)))) =
          PresentedGroup.of (sourceConditionalLabel m b) := by
  let β := Fin 5 × {σ : Equiv.Perm (Fin (m+1)) //
      σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}
  let input : β → (Set.range (polygonAssignment (initialTest a r)) →
      alternatingGroup (Fin (m+1))) := fun b =>
    polygonTableInput (initialTest a r) b.1 ⟨b.2.val,b.2.property.1⟩
  let w : β → FreeGroup (SourceGeneratorLabel m) :=
    fun b => FreeGroup.of (sourceConditionalLabel m b)
  have hw : ∀ b, FreeGroup.lift (alternatingGenerator a r m hm') (w b) =
      actualPolygonTableHom (initialTest a r) (input b) := by
    intro b
    rw [show w b = FreeGroup.of (sourceConditionalLabel m b) from rfl,
      FreeGroup.lift_apply_of]
    change _ = actualPolygonTableHom (initialTest a r)
      (polygonTableInput (initialTest a r) b.1 ⟨b.2.val,b.2.property.1⟩)
    rw [actualPolygonTableHom_input]
    rfl
  obtain ⟨L,hL⟩ := finite_table_with_inputs_eventually (alternatingGenerator a r m hm')
    (actualPolygonTableHom (initialTest a r)) input w hw
    (alternatingGenerator_surjective a r m hr hm hm')
  refine ⟨L,fun M hM => ?_⟩
  obtain ⟨ρ,hρ,hi⟩ := hL M hM
  refine ⟨ρ,hρ,?_,hi⟩
  intro s t hst
  apply actualPolygonTableHom_injective (initialTest a r)
  have hst' := congrArg (coverMap M (alternatingGenerator a r m hm')) hst
  exact (DFunLike.congr_fun hρ s).symm.trans (hst'.trans (DFunLike.congr_fun hρ t))

end SourceInitialPointwiseTable

end SimpleAmenable
end
end

end OAI
