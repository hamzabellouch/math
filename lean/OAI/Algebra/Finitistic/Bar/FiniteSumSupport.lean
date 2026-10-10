import OAI.Algebra.Finitistic.Bar.RecursiveTotalDifferential

namespace OAI
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u
variable {D : Type u} [Ring D]
variable {I : Type} [Finite I] [DecidableEq I] (V : I → ModuleCat.{u} D)
  (P : I → Prop) [DecidablePred P]

/-- Omitting zero summands is an isomorphism of ordinary direct sums. -/
def supportIso (hzero : ∀ i, ¬P i → IsZero (V i)) :
    ModuleCat.of D (⨁ i, V i) ≅ ModuleCat.of D (⨁ i : {i // P i}, V i.val) where
  hom := ModuleCat.ofHom (DirectSum.toModule D _ _ (fun i =>
    if h : P i then DirectSum.lof D {i // P i} (fun i => V i.val) ⟨i,h⟩ else 0))
  inv := ModuleCat.ofHom (DirectSum.toModule D _ _
    (fun i => DirectSum.lof D I (fun i => V i) i.val))
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro v
    by_cases h : P i
    · simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply, DirectSum.toModule_lof, dite_eq_left h,
        ModuleCat.hom_id, LinearMap.id_apply]
    · have hz : (𝟙 (V i)) = 0 := (hzero i h).eq_of_src _ _
      have hv : v=0 := congrArg (fun f : V i ⟶ V i => f.hom v) hz
      subst v
      simp
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro v
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.comp_apply, DirectSum.toModule_lof, dite_eq_left i.property,
      ModuleCat.hom_id, LinearMap.id_apply]
end DerivedBar.RecursiveTotal

end

end OAI
