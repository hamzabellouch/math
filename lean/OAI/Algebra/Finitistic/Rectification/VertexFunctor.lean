import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.VertexFunctor
universe u
variable {A B : Type u} [Ring A] [Ring B]
variable (β : B →+* A) (e : A) (he : e*e=e) (hc : ∀ b, e*β b=β b*e)

abbrev restricted (M : ModuleCat.{u} A) := (ModuleCat.restrictScalars β).obj M

/-- The original vertex action is linear for the commuting right restriction. -/
def action (M : ModuleCat.{u} A) : restricted β M →ₗ[B] restricted β M where
  toFun m := e • (m : M)
  map_add' x y := smul_add _ _ _
  map_smul' b m := by
    change e • (β b • (m : M)) = β b • (e • (m : M))
    rw [← mul_smul,← mul_smul,hc]

def fixed (M : ModuleCat.{u} A) : Submodule B (restricted β M) :=
  (action β e hc M - LinearMap.id).ker

@[simp] theorem mem_fixed (M : ModuleCat.{u} A) (m : restricted β M) :
    m ∈ fixed β e hc M ↔ e • (m : M) = m := by
  simp [fixed,action,sub_eq_zero]

/-- The genuine projection onto the vertex component. -/
def projection (M : ModuleCat.{u} A) : restricted β M →ₗ[B] fixed β e hc M :=
  (action β e hc M).codRestrict _ (by
    intro m
    rw [mem_fixed]
    change e • (e • (m : M)) = e • (m : M)
    rw [← mul_smul,he])

def inclusion (M : ModuleCat.{u} A) : fixed β e hc M →ₗ[B] restricted β M :=
  (fixed β e hc M).subtype

theorem projection_inclusion (M : ModuleCat.{u} A) :
    (projection β e he hc M).comp (inclusion β e hc M) = LinearMap.id := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  exact (mem_fixed β e hc M m.val).1 m.property

/-- Module maps restrict to the actual vertex fixed submodules. -/
def map {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    fixed β e hc M →ₗ[B] fixed β e hc N where
  toFun m := ⟨f.hom m.val,by
    apply (mem_fixed β e hc N _).2
    have hm := (mem_fixed β e hc M m.val).1 m.property
    exact (f.hom.map_smul e (m.val : M)).symm.trans (congrArg f.hom hm)⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' b x := by
    apply Subtype.ext
    change f.hom (β b • (x.val : M)) = β b • f.hom x.val
    exact f.hom.map_smul _ _

/-- The actual vertex-component functor; it retains the original right action. -/
def functor : ModuleCat.{u} A ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (fixed β e hc M)
  map f := ModuleCat.ofHom (map β e hc f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

instance additive : (functor β e hc).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

include he in
/-- Vertex components of right-projective modules are right-projective. -/
theorem projective (M : ModuleCat.{u} A) [Module.Projective B (restricted β M)] :
    Module.Projective B (fixed β e hc M) := by
  exact Module.Projective.of_split (inclusion β e hc M) (projection β e he hc M)
    (projection_inclusion β e he hc M)

include he in
/-- Applying a vertex component preserves actual short exact sequences. -/
theorem map_shortExact (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact) :
    (S.map (functor β e hc)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    constructor
    · intro hx
      have hx' : S.g.hom x.val = 0 := congrArg Subtype.val hx
      obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff S).1 hS.exact x.val hx'
      refine ⟨projection β e he hc S.X₁ y,?_⟩
      apply Subtype.ext
      change S.f.hom (e • y) = x.val
      rw [S.f.hom.map_smul,hy]
      exact (mem_fixed β e hc S.X₂ x.val).1 x.property
    · rintro ⟨y,rfl⟩
      apply Subtype.ext
      exact S.moduleCat_zero_apply y.val
  · intro x y h
    apply Subtype.ext
    apply hS.moduleCat_injective_f
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨y,hy⟩ := hS.moduleCat_surjective_g z.val
    refine ⟨projection β e he hc S.X₂ y,?_⟩
    apply Subtype.ext
    change S.g.hom (e • y) = z.val
    rw [S.g.hom.map_smul,hy]
    exact (mem_fixed β e hc S.X₃ z.val).1 z.property
end LittleFinitistic.VertexFunctor

end

end OAI
