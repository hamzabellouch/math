import OAI.Algebra.Finitistic.Bar.PatternPrefixCoordinates
import OAI.Algebra.Finitistic.Bar.BarCoordinateNaturality

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]
local notation "A" => TrivSqZeroExt D X


/-- The categorical X-bar pattern coordinates and the suffix formula have
exactly the same embedding into the original A bar, including the degree cast. -/
theorem embed_twoSidedBarPatternIso (i : ℕ) (p : List Bool)
    (v : ((BimoduleTensor.twoSidedBarFunctor k D X).obj
      (ModuleCat.of D (patternTerm k D X N p))).X i) :
    embed k D X N (true :: (List.replicate i false ++ p))
      ((twoSidedBarPatternIso k D X N i p).hom.hom v) =
    termCast k D X N
      (show (p.length+i)+1=(true :: (List.replicate i false ++ p)).length by simp; omega)
      (idealSuffixEmbed k D X N (patternTerm k D X N p) p.length i (embed k D X N p)
        ((twoSidedBarObjIso k D X (patternTerm k D X N p) i).hom.hom v)) := by
  let e := (termPatternIso k D X N i p).toLinearEquiv.restrictScalars k
  suffices h : ∀ w : X ⊗[k] term k D (patternTerm k D X N p) i,
      embed k D X N (true :: (List.replicate i false ++ p))
        (AlgebraTensorModule.congr (LinearEquiv.refl D X) e w) =
      termCast k D X N
        (show (p.length+i)+1=(true :: (List.replicate i false ++ p)).length by simp; omega)
        (idealSuffixEmbed k D X N (patternTerm k D X N p) p.length i (embed k D X N p) w) from
    h ((twoSidedBarObjIso k D X (patternTerm k D X N p) i).hom.hom v)
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul x w =>
    change (inr x : A) ⊗ₜ[k]
      embed k D X N (List.replicate i false ++ p) ((termPatternIso k D X N i p).hom.hom w) = _
    rw [embed_termPatternIso, idealSuffixEmbed_tmul]
    exact (termCast_tmul k D X N
      (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
      (show (p.length+i)+1=(List.replicate i false ++ p).length+1 by simp; omega)
      (inr x) (suffixEmbed k D X N _ p.length (embed k D X N p) i w)).symm
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The same compatibility for the final free D bar, before projecting its exterior slot. -/
theorem embed_freeBarPatternIso (i : ℕ) (p : List Bool)
    (v : ((barFunctor k D).obj (ModuleCat.of D (patternTerm k D X N p))).X i) :
    embed k D X N (List.replicate (i+1) false ++ p)
      ((freeBarPatternIso k D X N i p).hom.hom v) =
    termCast k D X N
      (show p.length+(i+1)=(List.replicate (i+1) false ++ p).length by simp; omega)
      (suffixEmbed k D X N (patternTerm k D X N p) p.length (embed k D X N p) (i+1)
        ((freeBarObjIso k D (patternTerm k D X N p) i).hom.hom v)) :=
  embed_termPatternIso k D X N (i+1) p
    ((freeBarObjIso k D (patternTerm k D X N p) i).hom.hom v)
end DerivedBar.ParityBridge

end

end OAI
