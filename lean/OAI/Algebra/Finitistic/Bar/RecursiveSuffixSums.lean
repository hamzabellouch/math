import OAI.Algebra.Finitistic.Bar.RecursiveSuffixEmbedding
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance recursiveSuffixSumsScalarModule (V : ModuleCat.{u} D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance recursiveSuffixSumsScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance recursiveSuffixSumsIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

/-- Finite coproduct extensionality also holds for k-linear maps out of a D bar. -/
theorem sum_hom_ext_scalar {I : Type} [Finite I] [DecidableEq I]
    (V : I → ModuleCat.{u} D) (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
    (W : ModuleCat.{u} k)
    {f g : G.obj (ModuleCat.of D (⨁ t, V t)) →ₗ[k] W}
    (h : ∀ t, f.comp ((G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t))).hom.restrictScalars k) =
      g.comp ((G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t))).hom.restrictScalars k)) :
    f=g := by
  let : Fintype I := Fintype.ofFinite I
  let R := ModuleCat.restrictScalars (algebraMap k D)
  have he : (ModuleCat.ofHom f : R.obj (G.obj (ModuleCat.of D (⨁ t, V t))) ⟶ W) =
      ModuleCat.ofHom g := by
    apply (isColimitOfPreserves (G ⋙ R) (ModuleCat.coproductCoconeIsColimit V)).hom_ext
    rintro ⟨t⟩
    exact ModuleCat.hom_ext (h t)
  exact congrArg ModuleCat.Hom.hom he

/-- Suffix insertion commutes with the actual finite-sum distribution map
appearing in the independently defined vertical differential. -/
theorem innerEmbedding_sumDesc (r n i q : ℕ) (h : i+q=n)
    (v : (RecursiveTotal.degreeFunctor B r i).obj (RecursiveTotal.flat B Z r q)) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.sumDesc (RecursiveTotal.summand B Z r q)
        (RecursiveTotal.degreeFunctor B r i)
        (fun t => RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩)).hom v) =
    termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (barSuffix k D X N (RecursiveTotal.flat B Z r q) (r+q) i
        (innerEmbedding k D X N r q) v) := by
  let C := termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
  let S := RecursiveTotal.sumDesc (RecursiveTotal.summand B Z r q)
    (RecursiveTotal.degreeFunctor B r i)
    (fun t => RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩)
  have he : (innerEmbedding k D X N (r+1) n).comp (S.hom.restrictScalars k) =
      C.comp (barSuffix k D X N (RecursiveTotal.flat B Z r q) (r+q) i
        (innerEmbedding k D X N r q)) := by
    apply sum_hom_ext_scalar k D (RecursiveTotal.summand B Z r q)
      (RecursiveTotal.degreeFunctor B r i) (term k A N ((r+1)+n))
    intro t
    ext w
    have hs := congrArg (fun f => f.hom w)
      (RecursiveTotal.lof_sumDesc (RecursiveTotal.summand B Z r q)
        (RecursiveTotal.degreeFunctor B r i)
        (fun t => RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩) t)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hs
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    change innerEmbedding k D X N (r+1) n (S.hom _) = C _
    erw [hs]
    erw [innerEmbedding_lof_succ k D X N r n i q h t w]
    change C _ = C (barSuffix k D X N (RecursiveTotal.flat B Z r q) (r+q) i
      (innerEmbedding k D X N r q) ((((XB).map (RecursiveTotal.lof B Z r q t)).f i).hom w))
    rw [barSuffix_map]
  exact congrArg (fun f => f v) he
end DerivedBar.ParityBridge

end

end OAI
