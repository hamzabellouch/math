import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormActualSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open Construction
open scoped BigOperators

def SmallUnitData.giantUnit {D P q : ℕ} {outerU xs : List SmallSlot} {v : ℤ}
    (h : SmallUnitData D P q outerU xs v) : (ZMod (∏ i, smallPrime xs outerU i))ˣ :=
  ((ZMod.isUnit_iff_coprime _ _).mpr (Nat.Coprime.prod_right (fun i _ =>
    (ZMod.isUnit_iff_coprime _ _).mp (h.giant i)))).unit

@[simp] theorem SmallUnitData.giantUnit_coe {D P q : ℕ} {outerU xs : List SmallSlot} {v : ℤ}
    (h : SmallUnitData D P q outerU xs v) :
    (h.giantUnit : ZMod (∏ i, smallPrime xs outerU i)) = q := IsUnit.unit_spec _

theorem actual_crtPairEquiv {D P q : ℕ} {outerU xs : List SmallSlot} {v : ℤ}
    (h : SmallUnitData D P q outerU xs v) :
    crtPairEquiv (smallPrime xs outerU) h.coprime ((P : ZMod (∏ i, smallPrime xs outerU i)), h.giantUnit) =
      smallResidues P q xs outerU h.giant := by
  funext i
  apply Prod.ext
  · simp only [crtPairEquiv_fst, map_natCast, smallResidues]
  · apply Units.ext
    simp only [crtPairEquiv_snd_coe, SmallUnitData.giantUnit_coe,
      map_natCast, smallResidues, IsUnit.unit_spec]

theorem diagonalSmallMultiplier_eq_crtTest (d : Decomposition) (D P q : ℕ)
    (outerU xs : List SmallSlot) (v : ℤ)
    [∀ i, Fact (smallPrime xs outerU i).Prime]
    (h : SmallUnitData D P q outerU xs v) :
    diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs =
      crtTest (smallPrime xs outerU) h.coprime (smallRetained xs outerU)
        (fun i => residueTransform d (smallPrime xs outerU i))
        (smallCoefficients D outerU xs v h.frequency h.denominator)
        ((P : ZMod (∏ i, smallPrime xs outerU i)), h.giantUnit) := by
  rw [crtTest, actual_crtPairEquiv]
  exact (actual_productTest_eq_of_outer_units d D P q outerU xs v
    h.frequency h.denominator h.giant h.outer).symm

theorem actual_small_modulus (a : State) (outerU xs : List SmallSlot)
    (hslots : a.small.Perm (outerU ++ xs)) :
    (∏ i, smallPrime xs outerU i) = (a.small.map SmallSlot.value).prod := by
  rw [smallPrime_product]
  have he := (hslots.map SmallSlot.value).prod_eq
  simpa only [List.map_append, List.prod_append, smallProduct, mul_comm] using he.symm

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
