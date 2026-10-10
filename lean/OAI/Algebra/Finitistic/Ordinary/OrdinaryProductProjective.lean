import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductComponent

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

abbrev firstInflation : ModuleCat.{v} L ⥤ ModuleCat.{v} (L × R) :=
  ModuleCat.restrictScalars (RingHom.fst L R)

variable {P : ModuleCat.{v} L} {M : ModuleCat.{v} (L × R)}

def intoFirst (g : (firstInflation L R).obj P ⟶ M) : P ⟶ firstObject L R M :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨g.hom x, by
        have h := g.hom.map_smul ((1,0) : L × R) x
        change g.hom ((1:L) • x) = ((1,0) : L × R) • g.hom x at h
        rw [one_smul] at h
        exact h.symm⟩
      map_add' := fun x y => Subtype.ext (g.hom.map_add x y)
      map_smul' := fun r x => Subtype.ext (g.hom.map_smul ((r,0) : L × R) x) }

theorem firstSpace_product_smul (d : L × R) (x : firstSpace L R M) :
    d • x.val = ((d.1,0) : L × R) • x.val := by
  have he : d * ((1,0) : L × R) = (d.1,0) := by ext <;> simp
  calc
    d • x.val = d • (((1,0) : L × R) • x.val) := by rw [x.property]
    _ = (d * ((1,0) : L × R)) • x.val := (mul_smul _ _ _).symm
    _ = _ := by rw [he]

def outOfFirst (g : P ⟶ firstObject L R M) : (firstInflation L R).obj P ⟶ M := by
  letI : Module (L × R) P := Module.compHom P (RingHom.fst L R)
  exact ModuleCat.ofHom (show (firstInflation L R).obj P →ₗ[L × R] M from
    { toFun := fun x => (g.hom x).val
      map_add' := fun x y => congrArg Subtype.val (g.hom.map_add x y)
      map_smul' := fun d x => by
        have h := congrArg Subtype.val (g.hom.map_smul d.1 x)
        exact h.trans (firstSpace_product_smul L R d (g.hom x)).symm })

/-- Inflation from one factor preserves actual projective objects. -/
theorem firstInflation_projective (P : ModuleCat.{v} L) [Projective P] :
    Projective ((firstInflation L R).obj P) := by
  refine ⟨fun g E he => ?_⟩
  let e : firstObject L R _ ⟶ firstObject L R _ := (firstFunctor L R).map E
  let g' := intoFirst L R g
  let : Epi e := (ModuleCat.epi_iff_surjective e).mpr
    (firstMap_surjective L R E ((ModuleCat.epi_iff_surjective E).mp he))
  let h := Projective.factorThru g' e
  refine ⟨outOfFirst L R h,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun f => f.hom x) (Projective.factorThru_comp g' e)
  exact congrArg Subtype.val hh
end LittleFinitistic.ProductModules

end

end OAI
