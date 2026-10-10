import OAI.Algebra.Finitistic.Bar.PatternSuffixFaces
import OAI.Algebra.Finitistic.Bar.PatternTensorCoherence

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
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]


omit [Module Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]
  [Module A N] [IsScalarTower k A N] in
/-- Prefix coordinates act literally on each tensor generator. -/
theorem termPatternIso_hom_tmul (i : ℕ) (p : List Bool) (d : D)
    (v : term k D (patternTerm k D X N p) i) :
    (termPatternIso k D X N (i+1) p).hom.hom (d ⊗ₜ[k] v) =
      d ⊗ₜ[k] (termPatternIso k D X N i p).hom.hom v := rfl

omit [Module A N] [IsScalarTower k A N] in
/-- The recursive suffix embedding is exactly the existing literal block embedding,
with every degree cast exposed. -/
theorem embed_termPatternIso (i : ℕ) (p : List Bool)
    (v : term k D (patternTerm k D X N p) i) :
    embed k D X N (List.replicate i false ++ p)
      ((termPatternIso k D X N i p).hom.hom v) =
    termCast k D X N (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
      (suffixEmbed k D X N (patternTerm k D X N p) p.length (embed k D X N p) i v) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [termPatternIso_hom_tmul, suffixEmbed_tmul]
      change (inl d : A) ⊗ₜ[k]
        embed k D X N (List.replicate i false ++ p) ((termPatternIso k D X N i p).hom.hom v) = _
      rw [ih]
      exact (termCast_tmul k D X N
        (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
        (show (p.length+i)+1=(List.replicate i false ++ p).length+1 by simp; omega)
        (inl d) (suffixEmbed k D X N _ p.length (embed k D X N p) i v)).symm
    | add v w hv hw => simp only [map_add, hv, hw]
end DerivedBar.ParityBridge

end

end OAI
