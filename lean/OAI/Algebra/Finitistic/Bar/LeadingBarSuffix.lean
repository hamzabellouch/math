import OAI.Algebra.Finitistic.Bar.RecursiveSuffixFaces

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance leadingBarSuffixScalarModule (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance leadingBarSuffixScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "DB" => barFunctor k D
local instance leadingBarSuffixInflatedModule : Module A N := inflatedModule D X N
local instance leadingBarSuffixInflatedTower : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- Retain the exterior D coefficient while applying an exact degree transport. -/
def outerCast {a b : ℕ} (h : a=b) :
    D ⊗[k] term k A N a →ₗ[D] D ⊗[k] term k A N b :=
  AlgebraTensorModule.lTensor D D (termCast k D X N h)

@[simp] theorem outerCast_refl (a : ℕ) : outerCast k D X N (rfl : a=a) = LinearMap.id := by
  ext value
  rfl

theorem outerCast_trans {a b c : ℕ} (h : a=b) (g : b=c)
    (v : D ⊗[k] term k A N a) :
    outerCast k D X N g (outerCast k D X N h v) = outerCast k D X N (h.trans g) v := by
  subst b; subst c
  simp only [outerCast_refl, LinearMap.id_apply]

theorem twoSidedParity_outerCast {a b : ℕ} (h : a=b) (h' : a+1=b+1)
    (v : D ⊗[k] term k A N (a+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N b (outerCast k D X N h' v) =
    outerCast k D X N h (SquareZero.multibarTwoSidedDifferential k D X N a v) := by
  subst b
  simp only [outerCast_refl, LinearMap.id_apply]

/-- The exterior free D bar uses its actual categorical coordinates. -/
def outerBarSuffix (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) :
    ((DB).obj V).X i →ₗ[D] D ⊗[k] term k A N (s+i) :=
  (outerSuffixEmbed k D X N V s i e).comp (Multibar.freeBarObjIso k D V i).hom.hom

theorem outerBarSuffix_map (V W : ModuleCat.{u} D) (s i : ℕ)
    (e : W →ₗ[k] term k A N s) (f : V ⟶ W) (v : ((DB).obj V).X i) :
    outerBarSuffix k D X N W s i e ((((DB).map f).f i).hom v) =
    outerBarSuffix k D X N V s i (e.comp (f.hom.restrictScalars k)) v := by
  have h := congrArg (fun g => g.hom v) (Multibar.freeBarObjIso_map k D V W f.hom i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold outerBarSuffix
  simp only [LinearMap.comp_apply]
  erw [h]
  exact outerSuffixEmbed_termMap k D X N V W s i e f.hom _

theorem parity_outerBarSuffix (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : V), e (d • v) = (inl d : A) • e v)
    (v : ((DB).obj V).X (i+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N ((s+1)+i)
      (outerBarSuffix k D X N V (s+1) (i+1) e v) =
    outerBarSuffix k D X N V (s+1) i e ((((DB).obj V).d (i+1) i).hom v) +
      (-1:k)^i • outerCast k D X N (show s+(i+1)=(s+1)+i by omega)
        (outerBarSuffix k D X N V s (i+1)
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v) := by
  have h := congrArg (fun g => g.hom v) (Multibar.freeBarObjIso_d k D V i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold outerBarSuffix
  simp only [LinearMap.comp_apply]
  erw [h]
  exact parity_outerSuffixEmbed k D X N V s i e he _

theorem parity_outerBarSuffix_zero (V : ModuleCat.{u} D) (s : ℕ)
    (e : V →ₗ[k] term k A N (s+1))
    (he : ∀ v, FreeBaseChange.coefficient (fstHom k D X) (term k A N s) (e v) = 0)
    (v : ((DB).obj V).X 0) :
    SquareZero.multibarTwoSidedDifferential k D X N s
      (outerBarSuffix k D X N V (s+1) 0 e v) =
    -outerBarSuffix k D X N V s 0
      ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v :=
  parity_outerSuffixEmbed_zero k D X N V s e he _

theorem outerBarSuffix_neg (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) :
    outerBarSuffix k D X N V s i (-e) = -outerBarSuffix k D X N V s i e := by
  ext v
  unfold outerBarSuffix
  simp only [LinearMap.neg_apply, LinearMap.comp_apply]
  generalize (Multibar.freeBarObjIso k D V i).hom.hom v = w
  induction w using TensorProduct.inductionOn with
  | tmul d w =>
    change d ⊗ₜ[k] suffixEmbed k D X N V s (-e) i w =
      -(d ⊗ₜ[k] suffixEmbed k D X N V s e i w)
    rw [← neg_one_smul k e, suffixEmbed_smul_map, neg_one_smul, TensorProduct.tmul_neg]
  | add v w hv hw => simp only [map_add, neg_add, hv, hw]

theorem outerBarSuffix_zero (V : ModuleCat.{u} D) (s i : ℕ) :
    outerBarSuffix k D X N V s i 0 = 0 := by
  ext v
  unfold outerBarSuffix
  simp only [LinearMap.zero_apply, LinearMap.comp_apply]
  generalize (Multibar.freeBarObjIso k D V i).hom.hom v = w
  induction w using TensorProduct.inductionOn with
  | tmul d w =>
    change d ⊗ₜ[k] suffixEmbed k D X N V s 0 i w = 0
    have hz := suffixEmbed_smul_map k D X N V s i (0:k) (0 : V →ₗ[k] term k A N s) w
    simp only [zero_smul] at hz
    rw [hz, TensorProduct.tmul_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

def outerBaseEmbed (i : ℕ) : D ⊗[k] term k D N i →ₗ[D] D ⊗[k] term k A N i :=
  AlgebraTensorModule.lTensor D D (baseEmbed k D X N i)

theorem coefficient_baseEmbed (i : ℕ) (v : term k D N (i+1)) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N i)
      (baseEmbed k D X N (i+1) v) = outerBaseEmbed k D X N i v := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [baseEmbed_tmul, FreeBaseChange.coefficient_tmul]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

theorem parity_outerBaseEmbed (i : ℕ) (v : D ⊗[k] term k D N (i+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N i (outerBaseEmbed k D X N (i+1) v) =
      outerBaseEmbed k D X N i (DerivedBar.differential k D N (i+1) v) := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    change SquareZero.multibarTwoSidedDifferential k D X N i
      (d ⊗ₜ[k] baseEmbed k D X N (i+1) v) = _
    rw [SquareZero.multibarTwoSidedDifferential_tmul, coefficient_baseEmbed,
      inflated_parity_baseEmbed, DerivedBar.differential_succ_tmul, map_sub, map_smul]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

theorem outerSuffixEmbed_id (i : ℕ) (v : D ⊗[k] term k D N i) :
    outerSuffixEmbed k D X N N 0 i LinearMap.id v =
      outerCast k D X N (Nat.zero_add i).symm (outerBaseEmbed k D X N i v) := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [outerSuffixEmbed_tmul, suffixEmbed_id]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

theorem parity_outerBarSuffix_terminal (i : ℕ) (v : ((DB).obj N).X (i+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N (0+i)
      (outerBarSuffix k D X N N 0 (i+1) LinearMap.id v) =
    outerBarSuffix k D X N N 0 i LinearMap.id ((((DB).obj N).d (i+1) i).hom v) := by
  have h := congrArg (fun g => g.hom v) (Multibar.freeBarObjIso_d k D N i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold outerBarSuffix
  simp only [LinearMap.comp_apply]
  erw [h]
  rw [outerSuffixEmbed_id, outerSuffixEmbed_id]
  erw [twoSidedParity_outerCast k D X N (Nat.zero_add i).symm
    (show i+1=(0+i)+1 by omega), parity_outerBaseEmbed]
end DerivedBar.ParityBridge

end

end OAI
