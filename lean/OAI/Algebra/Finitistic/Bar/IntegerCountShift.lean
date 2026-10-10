import OAI.Algebra.Finitistic.Bar.IntegerCountRestriction

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
local instance (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance (n r : ℕ) : DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

local notation "C" => ModuleCat D
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

theorem shapeCount_le {n r : ℕ} (p : Multibar.Indexed.Shape n r) : r≤n := by
  induction p <;> omega

theorem signedBlock_isZero_of_lt (n r : ℕ) (h : n<r) : IsZero ((K r).X n) := by
  have : IsEmpty (Multibar.Indexed.Shape n r) :=
    ⟨fun shape => (Nat.not_le_of_lt h) (shapeCount_le shape)⟩
  change IsZero (ModuleCat.of D (⨁ p : Multibar.Indexed.Shape n r, Multibar.Indexed.outerTensor k D X N p))
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual -r-shifted count complex is strictly zero in positive cochain
degrees, including the range cut off by the lower count bound. -/
theorem deshiftedCount_isZero_positive (r : ℕ) (j : ℤ) (hj : 0<j) :
    IsZero ((deshiftedCount k D X N r).X j) := by
  change IsZero (((K r).extend E).X (j + -(r:ℤ)))
  by_cases hle : j + -(r:ℤ) ≤ 0
  · let n := (-(j + -(r:ℤ))).toNat
    have hn : (E).f n=j + -(r:ℤ) := by
      change -(n:ℤ)=j + -(r:ℤ)
      dsimp [n]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hnr : n<r := by
      change -(n:ℤ)=j + -(r:ℤ) at hn
      omega
    exact (signedBlock_isZero_of_lt k D X N n r hnr).of_iso ((K r).extendXIso E hn)
  · exact (K r).isZero_extend_X E _ (fun i hi => by
      change -(i:ℤ)=j + -(r:ℤ) at hi
      omega)

instance deshiftedCount_strictSupport (r : ℕ) : (deshiftedCount k D X N r).IsStrictlySupported E where
  isZero j hj := deshiftedCount_isZero_positive k D X N r j (by
    by_contra h
    have hle : j≤0 := by omega
    apply hj (-j).toNat
    change -((-j).toNat:ℤ)=j
    rw [Int.toNat_of_nonneg (by omega)]
    omega)

/-- Extension of the genuine recursive complex is the actual -r shift of
the count complex. Strict support, not truncation by assumption, supplies the inverse. -/
def integerIndexedDeshiftedCountIso (r : ℕ) :
    (integerExtension D).obj (indexedMultibar k D X N r) ≅ deshiftedCount k D X N r :=
  (integerExtension D).mapIso (indexedDeshiftedCountIso k D X N r) ≪≫
    strictSupportExtensionIso E (deshiftedCount k D X N r)

/-- The manuscript's actual [r] cochain shift of the indexed recursive bar
is isomorphic to the entire signed count complex. -/
def integerIndexedCountShiftIso (r : ℕ) :
    ((integerExtension D).obj (indexedMultibar k D X N r))⟦(r:ℤ)⟧ ≅
      (integerExtension D).obj (K r) :=
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (r:ℤ)).mapIso
    (integerIndexedDeshiftedCountIso k D X N r) ≪≫
      ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) (-(r:ℤ)) (r:ℤ) 0 (by omega)).symm.app
        ((integerExtension D).obj (K r))) ≪≫
      (CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app ((integerExtension D).obj (K r))
end DerivedBar.ParityBridge

end

end OAI
