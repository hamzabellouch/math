import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration

def extendedRootSmallTest (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v)
    (z : ZMod (rootModulus h) × ZMod (rootModulus h)) : ℝ := by
  classical
  exact if hq : IsUnit z.2 then
    rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ (z.1,hq.unit)
  else 0

theorem extendedRootSmallTest_bounds (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v)
    (z : ZMod (rootModulus h) × ZMod (rootModulus h)) :
    0 ≤ extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z ∧
    extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z ≤ (rootModulus h:ℝ) := by
  unfold extendedRootSmallTest
  split
  · exact rootSmallTest_bounds d h outerU xs hslots D P₀ q₀ v hu₀ _
  · exact ⟨le_refl _,Nat.cast_nonneg _⟩

theorem extendedRootSmallTest_norm_le (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v)
    (z : ZMod (rootModulus h) × ZMod (rootModulus h)) :
    ‖(extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z:ℂ)‖ ≤ (rootModulus h:ℝ) := by
  have hb := extendedRootSmallTest_bounds d h outerU xs hslots D P₀ q₀ v hu₀ z
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2

theorem rootResidueIndicator_mul_extendedRootSmallTest (d : Decomposition) {l : ℕ}
    (h : History l) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs)) (D P₀ q₀ : ℕ) (v : ℤ)
    [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v)
    (z : ZMod (rootModulus h) × ZMod (rootModulus h)) :
    rootResidueIndicator h z *
      (extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z:ℂ) =
      (extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z:ℂ) := by
  unfold extendedRootSmallTest
  split
  · rename_i hq
    simpa only [hq.unit_spec] using
      rootResidueIndicator_mul_rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀
        (z.1,hq.unit)
  · simp

theorem smallPrime_dvd_root {l : ℕ} (h : History l) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs)) (i : SmallIndex xs outerU) :
    smallPrime xs outerU i ∣ rootModulus h := by
  rw [←small_modulus_eq_root h outerU xs hslots]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem smallPrime_isUnit_of_root {l : ℕ} (h : History l) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs)) (P : ℕ)
    (hp : IsUnit (P:ZMod (rootModulus h))) (i : SmallIndex xs outerU) :
    IsUnit (P:ZMod (smallPrime xs outerU i)) := by
  simpa only [map_natCast] using hp.map
    (ZMod.castHom (smallPrime_dvd_root h outerU xs hslots i)
      (ZMod (smallPrime xs outerU i)))

theorem extendedRootSmallTest_natCast (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v)
    (hP : IsUnit (P:ZMod (rootModulus h))) (hq : IsUnit (q:ZMod (rootModulus h))) :
    extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀
      ((P:ZMod (rootModulus h)),(q:ZMod (rootModulus h))) =
      diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs := by
  let hu := hu₀.changeGiants P q (smallPrime_isUnit_of_root h outerU xs hslots q hq)
    (fun i => smallPrime_isUnit_of_root h outerU xs hslots P hP (.inr i))
  have he : actualRootDraw h outerU xs hslots D P q v hu =
      ((P:ZMod (rootModulus h)),hq.unit) := by
    apply Prod.ext
    · exact actualRootDraw_fst_natCast h outerU xs hslots D P q v hu
    · apply Units.ext
      rw [actualRootDraw_snd_coe_natCast,hq.unit_spec]
  simpa only [extendedRootSmallTest,dite_eq_left hq,←he] using
    rootSmallTest_reference_actualRootDraw d h outerU xs hslots D P₀ q₀ P q v hu₀ hu

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
