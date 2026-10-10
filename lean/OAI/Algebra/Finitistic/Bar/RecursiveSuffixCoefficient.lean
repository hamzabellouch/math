import OAI.Algebra.Finitistic.Bar.RecursiveSuffixTotal

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance recursiveSuffixCoefficientIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

theorem coefficient_termCast {a b : ℕ} (h : a=b) (h' : a+1=b+1)
    (v : term k A N (a+1)) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N b) (termCast k D X N h' v) =
      AlgebraTensorModule.lTensor D D (termCast k D X N h)
        (FreeBaseChange.coefficient (fstHom k D X) (term k A N a) v) := by
  subst b
  simp only [termCast, LinearMap.id_apply, AlgebraTensorModule.lTensor_id]

/-- The first X factor is killed by the exterior projection A -> D. -/
theorem barSuffix_coefficient_zero (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) (v : ((XB).obj V).X i) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N (s+i))
      (barSuffix k D X N V s i e v) = 0 := by
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using TensorProduct.inductionOn with
  | tmul x w =>
    rw [idealSuffixEmbed_tmul, FreeBaseChange.coefficient_tmul]
    simp
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

/-- The exterior endpoint vanishes at every positive suffix degree, including
zero input summands when no X has yet been inserted. -/
theorem innerEmbedding_coefficient_of_pos (r n s : ℕ) (hs : r+n=s+1)
    (v : RecursiveTotal.flat B Z r n) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N s)
      (termCast k D X N hs (innerEmbedding k D X N r n v)) = 0 := by
  cases r with
  | zero =>
    cases n with
    | zero => omega
    | succ n => simp only [innerEmbedding, LinearMap.zero_apply, map_zero]
  | succ r =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | of t v =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      change FreeBaseChange.coefficient (fstHom k D X) (term k A N s)
        (termCast k D X N hs (innerEmbedding k D X N (r+1) n
          ((RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩).hom v))) = 0
      erw [innerEmbedding_lof_succ k D X N r n i q h t v]
      erw [termCast_trans k D X N (show ((r+q)+i)+1=(r+1)+n by omega) hs]
      erw [coefficient_termCast k D X N (show (r+q)+i=s by omega)
        (show ((r+q)+i)+1=s+1 by omega)]
      erw [barSuffix_coefficient_zero k D X N (RecursiveTotal.summand B Z r q t)
        (r+q) i _ v]
      exact map_zero _

theorem innerTotalEmbedding_coefficient_of_pos (r n s : ℕ) (hs : r+n=s+1)
    (v : (RecursiveTotal.iter B Z r).X n) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N s)
      (termCast k D X N hs (innerTotalEmbedding k D X N r n v)) = 0 :=
  innerEmbedding_coefficient_of_pos k D X N r n s hs _

theorem innerEmbedding_coefficient_zero (r n : ℕ)
    (v : RecursiveTotal.flat B Z (r+1) n) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N (r+n))
      (termCast k D X N (show (r+1)+n=(r+n)+1 by omega)
        (innerEmbedding k D X N (r+1) n v)) = 0 :=
  innerEmbedding_coefficient_of_pos k D X N (r+1) n (r+n) (by omega) v

theorem innerTotalEmbedding_coefficient_zero (r n : ℕ)
    (v : (RecursiveTotal.iter B Z (r+1)).X n) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N (r+n))
      (termCast k D X N (show (r+1)+n=(r+n)+1 by omega)
        (innerTotalEmbedding k D X N (r+1) n v)) = 0 :=
  innerTotalEmbedding_coefficient_of_pos k D X N (r+1) n (r+n) (by omega) v
end DerivedBar.ParityBridge

end

end OAI
