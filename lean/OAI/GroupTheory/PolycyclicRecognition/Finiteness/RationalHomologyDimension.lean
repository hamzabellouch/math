import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareTopHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneEndomorphisms
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalNilpotentHomologyVanishing
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

namespace OAI

/-! # Detecting dimension using rational homology with coefficients

Shapiro's lemma passes a uniform bound to subgroups. The orientation module
detects the dimension of an integral Poincare duality group even after
rationalization. No finiteness of coefficient representations is required.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

def RationalHomologyDimensionLE (G : Type) [Group G] (d : ℕ) : Prop :=
  ∀ (A : Rep ℤ G) (i : ℕ), d < i →
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i))

theorem RationalHomologyDimensionLE.subgroup {d : ℕ}
    (hG : RationalHomologyDimensionLE G d) (H : Subgroup G) :
    RationalHomologyDimensionLE H d := by
  classical
  intro A i hi
  exact (hG (Rep.ind H.subtype A) i hi).of_iso
    (rationalModuleFunctor.mapIso (groupHomology.indIso H A i).symm)

theorem IsIntegralPoincareDualityGroup.dimension_le_of_rational_homology_bound
    {n d : ℕ} (hG : IsIntegralPoincareDualityGroup G n)
    (hd : RationalHomologyDimensionLE G d) : n ≤ d := by
  by_contra hnd
  obtain ⟨D, ⟨eD⟩, hD⟩ := hG.topHomology_orientation
  obtain ⟨eH⟩ := hD D
  let e : groupHomology D n ≃ₗ[ℤ] ℤ :=
    eH.trans (rankOneEndomorphismsEquiv D eD)
  let eQ : (ℚ ⊗[ℤ] groupHomology D n) ≃ₗ[ℤ] ℚ :=
    ((e.baseChange ℤ ℚ _ _).restrictScalars ℤ).trans (TensorProduct.rid ℤ ℚ)
  have hz := hd D n (by omega)
  let : Subsingleton (ℚ ⊗[ℤ] groupHomology D n) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  have h : (1 : ℚ) = 0 := by
    calc
      1 = eQ (eQ.symm 1) := (eQ.apply_symm_apply 1).symm
      _ = eQ 0 := congrArg eQ (Subsingleton.elim _ _)
      _ = 0 := map_zero eQ
  exact one_ne_zero h

end PolycyclicRecognition

end

end OAI
