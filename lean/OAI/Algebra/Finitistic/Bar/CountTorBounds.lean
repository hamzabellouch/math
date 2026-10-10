import OAI.Algebra.Finitistic.Bar.CountHomologyDetection

namespace OAI
open CategoryTheory CategoryTheory.Limits TrivSqZeroExt
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
local notation "S" => SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N)
local notation "T" => tensorBarComplex k A D N (fstHom k D X)

/-- Exact degreewise vanishing criterion for actual base-change Tor, in terms
of the original integer-derived count objects. -/
theorem baseChangeTor_zero_iff_counts (n : ℕ) :
    IsZero (((Balanced.tensorFunctor (fstHom k D X)).leftDerived n).obj (ModuleCat.of A N)) ↔
      ∀ r, IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n:ℤ))).obj
        ((integerQ D).obj (S r))) := by
  constructor
  · intro hz r
    by_contra hr
    exact baseChangeTor_nonzero_of_count k D X N r n hr hz
  · exact baseChangeTor_zero_of_counts k D X N n

/-- A uniform upper bound on the original count homologies is a uniform bound
on actual base-change Tor. This is the consumer for Native's uniform count window. -/
theorem baseChangeTor_bounded_of_counts (B : ℕ)
    (h : ∀ r n, B < n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n:ℤ))).obj
        ((integerQ D).obj (S r)))) :
    ∀ n, B < n →
      IsZero (((Balanced.tensorFunctor (fstHom k D X)).leftDerived n).obj (ModuleCat.of A N)) :=
  fun n hn => baseChangeTor_zero_of_counts k D X N n (fun r => h r n hn)

/-- Any nonzero count homology witness above r gives a nonzero actual Tor
witness above r, without replacing projective dimension by an invented invariant. -/
theorem baseChangeTor_nonzero_ge_of_count (r : ℕ)
    (h : ∃ n, r ≤ n ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n:ℤ))).obj
        ((integerQ D).obj (S r)))) :
    ∃ n, r ≤ n ∧
      ¬ IsZero (((Balanced.tensorFunctor (fstHom k D X)).leftDerived n).obj (ModuleCat.of A N)) := by
  obtain ⟨n, hn, hnonzero⟩ := h
  exact ⟨n, hn, baseChangeTor_nonzero_of_count k D X N r n hnonzero⟩
end DerivedBar.ParityBridge

end

end OAI
