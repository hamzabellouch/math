import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CohomologicalFiniteness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Finsupp.Defs

namespace OAI

/-! # Exact direct sums of integral modules -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

def moduleFinsuppFunctor (k : Type) [Ring k] (α : Type) : ModuleCat k ⥤ ModuleCat k where
  obj M := ModuleCat.of k (α →₀ M)
  map f := ModuleCat.ofHom (Finsupp.mapRange.linearMap f.hom)
  map_id _ := by ext x i; rfl
  map_comp _ _ := by ext x i; rfl

instance (k : Type) [Ring k] (α : Type) : (moduleFinsuppFunctor k α).Additive where
  map_add {X Y} f g := by
    dsimp only [moduleFinsuppFunctor]
    ext x i
    rfl

theorem moduleFinsuppFunctor_map_exact (k : Type) [Ring k] (α : Type)
    (S : ShortComplex (ModuleCat k))
    (hS : S.Exact) : (S.map (moduleFinsuppFunctor k α)).Exact := by
  classical
  let preimage (x : S.X₂) : S.X₁ :=
    if x = 0 then 0 else if h : S.g.hom x = 0 then
      ((ShortComplex.moduleCat_exact_iff S).mp hS x h).choose else 0
  have hzero : preimage 0 = 0 := by simp [preimage]
  have hpre (x : S.X₂) (hx : S.g.hom x = 0) : S.f.hom (preimage x) = x := by
    by_cases hz : x = 0
    · simp [preimage, hz]
    · simp only [preimage, ite_eq_right hz, dite_eq_left hx]
      exact ((ShortComplex.moduleCat_exact_iff S).mp hS x hx).choose_spec
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x : α →₀ S.X₂,
    Finsupp.mapRange S.g.hom (map_zero _) x = 0 →
      ∃ y : α →₀ S.X₁, Finsupp.mapRange S.f.hom (map_zero _) y = x
  intro x hx
  refine ⟨Finsupp.mapRange preimage hzero x, ?_⟩
  ext i
  have hi := congrArg (fun y : α →₀ S.X₃ => y i) hx
  change S.g.hom (x i) = 0 at hi
  exact hpre (x i) hi

instance (k : Type) [Ring k] (α : Type) : (moduleFinsuppFunctor k α).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (moduleFinsuppFunctor_map_exact k α)

abbrev integralFinsuppFunctor (α : Type) := moduleFinsuppFunctor ℤ α

end PolycyclicRecognition

end

end OAI
