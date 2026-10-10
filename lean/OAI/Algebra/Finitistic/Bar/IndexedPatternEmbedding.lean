import OAI.Algebra.Finitistic.Bar.SupportedInnerCoordinates
import OAI.Algebra.Finitistic.Bar.LeadingTotalComparison

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance indexedPatternEmbeddingScalarModule (V : ModuleCat.{u} D) :
    Module k V := BimoduleTensor.scalarModule k D V
local instance indexedPatternEmbeddingScalarTower (V : ModuleCat.{u} D) :
    IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance indexedPatternEmbeddingIndexDecidableEq (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance indexedPatternEmbeddingInflatedModule : Module A N := inflatedModule D X N
local instance indexedPatternEmbeddingInflatedScalarTower : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

theorem eqToHom_tensor_tmul (L : Type u) [AddCommGroup L] [Module k L]
    (V W : ModuleCat.{u} k) (h : V=W) (x : L) (v : V) :
    (eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of k (L ⊗[k] T)) h)).hom (x ⊗ₜ[k] v) =
      x ⊗ₜ[k] (eqToHom h).hom v := by
  subst W
  rfl

theorem eqToHom_outer_tmul (V W : ModuleCat.{u} k) (h : V=W) (d : D) (v : V) :
    (eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of D (D ⊗[k] T)) h)).hom (d ⊗ₜ[k] v) =
      d ⊗ₜ[k] (eqToHom h).hom v := by
  subst W
  rfl

/-- The old indexed inclusion and old list-pattern embedding agree; transports
come solely from the proved equality of their tensor objects and their degrees. -/
theorem indexedInclusion_toList {n r : ℕ} (p : Multibar.Indexed.Shape n r)
    (v : Multibar.Indexed.tensor k D X N p) :
    Multibar.Indexed.inclusion k D X N p v =
      termCast k D X N (Multibar.Indexed.length_toList p)
        (embed k D X N (Multibar.Indexed.toList p)
          ((eqToHom (Multibar.Indexed.tensor_toList k D X N p)).hom v)) := by
  induction p with
  | nil => rfl
  | @base n r p ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      change (inl d : A) ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
        termCast k D X N (show (false :: Multibar.Indexed.toList p).length=n+1 by simp)
          (embed k D X N (false :: Multibar.Indexed.toList p)
            ((eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of k (D ⊗[k] T))
              (Multibar.Indexed.tensor_toList k D X N p))).hom (d ⊗ₜ[k] v)))
      rw [eqToHom_tensor_tmul k D (Multibar.Indexed.tensor k D X N p)
        (patternTerm k D X N (Multibar.Indexed.toList p))
        (Multibar.Indexed.tensor_toList k D X N p) d v]
      change (inl d : A) ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
        termCast k D X N (show (false :: Multibar.Indexed.toList p).length=n+1 by simp) ((inl d : A) ⊗ₜ[k] _)
      rw [ih]
      exact (termCast_tmul k D X N (Multibar.Indexed.length_toList p)
        (by simp) _ _).symm
    | add v w hv hw => simp only [map_add, hv, hw]
  | @ideal n r p ih =>
    induction v using TensorProduct.inductionOn with
    | tmul x v =>
      change (inr x : A) ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
        termCast k D X N (show (true :: Multibar.Indexed.toList p).length=n+1 by simp)
          (embed k D X N (true :: Multibar.Indexed.toList p)
            ((eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of k (X ⊗[k] T))
              (Multibar.Indexed.tensor_toList k D X N p))).hom (x ⊗ₜ[k] v)))
      rw [eqToHom_tensor_tmul k X (Multibar.Indexed.tensor k D X N p)
        (patternTerm k D X N (Multibar.Indexed.toList p))
        (Multibar.Indexed.tensor_toList k D X N p) x v]
      change (inr x : A) ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
        termCast k D X N (show (true :: Multibar.Indexed.toList p).length=n+1 by simp) ((inr x : A) ⊗ₜ[k] _)
      rw [ih]
      exact (termCast_tmul k D X N (Multibar.Indexed.length_toList p)
        (by simp) _ _).symm
    | add v w hv hw => simp only [map_add, hv, hw]

theorem outerInclusion_toList {n r : ℕ} (p : Multibar.Indexed.Shape n r)
    (v : Multibar.Indexed.outerTensor k D X N p) :
    Multibar.Indexed.outerInclusion k D X N p v =
      outerCast k D X N (Multibar.Indexed.length_toList p)
        (AlgebraTensorModule.lTensor D D (embed k D X N (Multibar.Indexed.toList p))
          ((eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of D (D ⊗[k] T))
            (Multibar.Indexed.tensor_toList k D X N p))).hom v)) := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [eqToHom_outer_tmul k D (Multibar.Indexed.tensor k D X N p)
      (patternTerm k D X N (Multibar.Indexed.toList p))
      (Multibar.Indexed.tensor_toList k D X N p) d v]
    change d ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
      d ⊗ₜ[k] termCast k D X N _
        (embed k D X N (Multibar.Indexed.toList p)
          ((eqToHom (Multibar.Indexed.tensor_toList k D X N p)).hom v))
    rw [indexedInclusion_toList]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem outerInclusion_pattern {n r : ℕ} (s : Multibar.Indexed.Shape n r)
    (p : List Bool) (hp : Multibar.Indexed.toList s=p)
    (ht : Multibar.Indexed.tensor k D X N s=patternTerm k D X N p)
    (hl : p.length=n) (v : Multibar.Indexed.outerTensor k D X N s) :
    Multibar.Indexed.outerInclusion k D X N s v =
      outerCast k D X N hl (AlgebraTensorModule.lTensor D D (embed k D X N p)
        ((eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of D (D ⊗[k] T)) ht)).hom v)) := by
  subst p
  exact outerInclusion_toList k D X N s v
end DerivedBar.ParityBridge

end

end OAI
