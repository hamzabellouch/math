import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ResolvedBoolean

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FinitePrimitiveResolution
variable {X ι : Type*}

theorem finite_resolving_subfamily (U : ι → Set X) {V : Set X}
    (hV : V ∈ BooleanSubalgebra.closure (Set.range U)) :
    ∃ S : Finset ι, ResolvedBy (fun i : S => U i.val) V := by
  classical
  induction hV using BooleanSubalgebra.closure_bot_sup_induction with
  | mem V h =>
    obtain ⟨i,rfl⟩ := h
    exact ⟨{i},fun x y he => he ⟨i,Finset.mem_singleton_self i⟩⟩
  | bot => exact ⟨∅,fun _ _ _ => Iff.rfl⟩
  | sup V W _ _ ihV ihW =>
    obtain ⟨S,hS⟩ := ihV
    obtain ⟨T,hT⟩ := ihW
    refine ⟨S ∪ T,fun x y he => or_congr (hS x y ?_) (hT x y ?_)⟩
    · intro i
      exact he ⟨i.val,Finset.mem_union_left _ i.property⟩
    · intro i
      exact he ⟨i.val,Finset.mem_union_right _ i.property⟩
  | compl V _ ih =>
    obtain ⟨S,hS⟩ := ih
    exact ⟨S,fun x y he => not_congr (hS x y he)⟩

noncomputable def translatedPrimitiveAlgebra (a : ℕ) (r : CutRing) :
    BooleanSubalgebra (Set (GenericSquare a)) :=
  BooleanSubalgebra.closure (Set.range fun p : Fin 5 × (CutRing × CutRing) =>
    (spatialTranslate p.2 (initialTest a r p.1)).val)

theorem translatedPrimitiveAlgebra_test (a : ℕ) (r : CutRing)
    (p : Fin 5 × (CutRing × CutRing)) :
    (spatialTranslate p.2 (initialTest a r p.1)).val ∈ translatedPrimitiveAlgebra a r :=
  BooleanSubalgebra.subset_closure ⟨p,rfl⟩

theorem translatedPrimitiveAlgebra_translate (a : ℕ) (r : CutRing)
    (u : CutRing × CutRing) {V : Set (GenericSquare a)}
    (hV : V ∈ translatedPrimitiveAlgebra a r) :
    translate a u ⁻¹' V ∈ translatedPrimitiveAlgebra a r := by
  induction hV using BooleanSubalgebra.closure_bot_sup_induction with
  | mem V h =>
    obtain ⟨p,rfl⟩ := h
    have he : translate a u ⁻¹' (spatialTranslate p.2 (initialTest a r p.1)).val =
        (spatialTranslate (p.2-u) (initialTest a r p.1)).val := by
      ext x
      simp only [spatialTranslate,Set.mem_preimage,← translate_add]
      abel_nf
    rw [he]
    exact translatedPrimitiveAlgebra_test a r (p.1,p.2-u)
  | bot => exact BooleanSubalgebra.bot_mem
  | sup V W _ _ ihV ihW => exact BooleanSubalgebra.sup_mem ihV ihW
  | compl V _ ih => exact BooleanSubalgebra.compl_mem ih

theorem translatedPrimitiveAlgebra_initial (a : ℕ) (r : CutRing) (j : Fin 5) :
    (initialTest a r j).val ∈ translatedPrimitiveAlgebra a r := by
  have h := translatedPrimitiveAlgebra_test a r (j,0)
  have he : (spatialTranslate (0:CutRing × CutRing) (initialTest a r j)).val =
      (initialTest a r j).val := by
    ext p
    simp [spatialTranslate,translate_zero]
  rwa [he] at h

theorem polygon_finite_primitive_resolution {a : ℕ} (r : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (V : polygonAlgebra a) :
    ∃ S : Finset (Fin 5 × (CutRing × CutRing)),
      ResolvedBy (fun p : S => (spatialTranslate p.val.2 (initialTest a r p.val.1)).val) V.val := by
  apply finite_resolving_subfamily (fun p : Fin 5 × (CutRing × CutRing) =>
    (spatialTranslate p.2 (initialTest a r p.1)).val)
  let B := translatedPrimitiveAlgebra a r
  have ht := fun u U hU => translatedPrimitiveAlgebra_translate a r u (V := U) hU
  have hcoord (j : Fin 2) (z : CutRing) :
      halfPlane a (Fin.castLE (by omega) j) z ∈ B := by
    apply coordinate_cuts_generated B j ht
    fin_cases j
    · exact translatedPrimitiveAlgebra_initial a r 1
    · exact translatedPrimitiveAlgebra_initial a r 2
  apply polygon_induction (P := fun U => U ∈ B) ?_ BooleanSubalgebra.bot_mem
    (fun _ _ hU hV => BooleanSubalgebra.sup_mem hU hV)
    (fun _ hU => BooleanSubalgebra.compl_mem hU) V.property
  intro j z
  fin_cases j
  · exact hcoord 0 z
  · exact hcoord 1 z
  · exact slope_cuts_generated r hr B ht hcoord 2 (Or.inl rfl)
      (translatedPrimitiveAlgebra_initial a r 3) z
  · exact slope_cuts_generated r hr B ht hcoord 3 (Or.inr rfl)
      (translatedPrimitiveAlgebra_initial a r 4) z

end FinitePrimitiveResolution

end SimpleAmenable
end
end

end OAI
