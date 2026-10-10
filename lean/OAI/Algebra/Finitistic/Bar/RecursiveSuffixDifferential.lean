import OAI.Algebra.Finitistic.Bar.RecursiveSuffixFaces
import OAI.Algebra.Finitistic.Bar.RecursiveSuffixSums

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance recursiveSuffixDifferentialScalarModule (V : ModuleCat.{u} D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance recursiveSuffixDifferentialScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance recursiveSuffixDifferentialIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local instance recursiveSuffixDifferentialInflatedModule : Module A N := inflatedModule D X N
local instance recursiveSuffixDifferentialInflatedScalarTower : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- The actual horizontal differential followed by the complete suffix embedding. -/
theorem innerEmbedding_horizontal (r n i q : ℕ) (h : (i+1)+q=n+1)
    (t : RecursiveTotal.Index r q)
    (v : (RecursiveTotal.degreeFunctor B r (i+1)).obj (RecursiveTotal.summand B Z r q t)) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.horizontal B Z r n (i+1) q h t).hom v) =
    termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (barSuffix k D X N (RecursiveTotal.summand B Z r q t) (r+q) i
        ((innerEmbedding k D X N r q).comp
          ((RecursiveTotal.lof B Z r q t).hom.restrictScalars k))
        ((((XB).obj (RecursiveTotal.summand B Z r q t)).d (i+1) i).hom v)) := by
  simp only [RecursiveTotal.horizontal]
  exact innerEmbedding_lof_succ k D X N r n i q (by omega) t _

/-- The actual signed vertical face is computed after distribution over the
whole inner sum, rather than on an assumed single supported output summand. -/
theorem innerEmbedding_vertical (r n i q : ℕ) (h : i+(q+1)=n+1)
    (t : RecursiveTotal.Index r (q+1))
    (d : ∀ q, RecursiveTotal.flat B Z r (q+1) ⟶ RecursiveTotal.flat B Z r q)
    (v : (RecursiveTotal.degreeFunctor B r i).obj (RecursiveTotal.summand B Z r (q+1) t)) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.vertical B Z r n i (q+1) h t d).hom v) =
    (-1:k)^i • termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (barSuffix k D X N (RecursiveTotal.summand B Z r (q+1) t) (r+q) i
        ((innerEmbedding k D X N r q).comp
          ((RecursiveTotal.lof B Z r (q+1) t ≫ d q).hom.restrictScalars k)) v) := by
  change innerEmbedding k D X N (r+1) n
    (((-1:ℤˣ)^i) •
      ((RecursiveTotal.sumDesc (RecursiveTotal.summand B Z r q)
        (RecursiveTotal.degreeFunctor B r i)
        (fun s => RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,by omega⟩,s⟩)).hom
          (((RecursiveTotal.degreeFunctor B r i).map
            (RecursiveTotal.lof B Z r (q+1) t ≫ d q)).hom v))) = _
  rw [totalSign_smul k (RecursiveTotal.flat B Z (r+1) n), map_smul,
    innerEmbedding_sumDesc]
  change (-1:k)^i • termCast k D X N _
    (barSuffix k D X N (RecursiveTotal.flat B Z r q) (r+q) i
      (innerEmbedding k D X N r q)
      ((((XB).map (RecursiveTotal.lof B Z r (q+1) t ≫ d q)).f i).hom v)) = _
  rw [barSuffix_map]

/-- Evaluation of the independently recursive differential on one input summand. -/
theorem innerEmbedding_differential_lof (r n i q : ℕ) (h : i+q=n+1)
    (t : RecursiveTotal.Index r q)
    (v : RecursiveTotal.summand B Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.differential B Z (r+1) n).hom
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩).hom v)) =
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.horizontal B Z r n i q h t).hom v) +
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.vertical B Z r n i q h t (RecursiveTotal.differential B Z r)).hom v) := by
  have he := congrArg (fun f => f.hom v)
    (RecursiveTotal.lof_differential_succ B Z r n i q h t)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he
  erw [ModuleCat.hom_add, LinearMap.add_apply] at he
  erw [he, map_add]
  rfl

/-- Degree transports compose by equality elimination alone. -/
theorem termCast_trans {a b c : ℕ} (h : a=b) (g : b=c) (v : term k A N a) :
    termCast k D X N g (termCast k D X N h v) = termCast k D X N (h.trans g) v := by
  subst b; subst c
  rfl

/-- Composition of the induction hypothesis with an actual summand inclusion. -/
theorem innerEmbedding_suffix_induction (r q : ℕ) (t : RecursiveTotal.Index r (q+1))
    (ih : ∀ (v : RecursiveTotal.flat B Z r (q+1)),
      SquareZero.multibarAugmentedDifferential k D X N (r+q)
        (innerEmbedding k D X N r (q+1) v) =
      -innerEmbedding k D X N r q ((RecursiveTotal.differential B Z r q).hom v)) :
    (SquareZero.multibarAugmentedDifferential k D X N (r+q)).comp
      ((innerEmbedding k D X N r (q+1)).comp
        ((RecursiveTotal.lof B Z r (q+1) t).hom.restrictScalars k)) =
    -((innerEmbedding k D X N r q).comp
      ((RecursiveTotal.lof B Z r (q+1) t ≫ RecursiveTotal.differential B Z r q).hom.restrictScalars k)) := by
  ext v
  exact ih ((RecursiveTotal.lof B Z r (q+1) t).hom v)
end DerivedBar.ParityBridge

end

end OAI
