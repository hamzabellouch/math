import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallAverageVanishing

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration

def mixedCongr {a b : ℕ} (h : a=b) :
    (ZMod a × (ZMod a)ˣ) ≃ (ZMod b × (ZMod b)ˣ) :=
  (ZMod.ringEquivCongr h).toEquiv.prodCongr
    (Units.mapEquiv (ZMod.ringEquivCongr h).toMulEquiv).toEquiv

theorem guardIndicator_mixedCongr {a b : ℕ} (h : a=b)
    (z : ZMod a × (ZMod a)ˣ) :
    guardIndicator (IsUnit (mixedCongr h z).1 ∧
      IsUnit ((mixedCongr h z).2 : ZMod b)) =
    guardIndicator (IsUnit z.1 ∧ IsUnit (z.2 : ZMod a)) := by
  subst b
  simp [mixedCongr,ZMod.ringEquivCongr_refl]

theorem small_modulus_eq_root {l : ℕ} (h : History l) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs)) :
    (∏i,smallPrime xs outerU i)=rootModulus h :=
  actual_small_modulus h.root outerU xs hslots

def rootSmallEquiv {l : ℕ} (h : History l) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs)) :
    (ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ) ≃
      (ZMod (∏i,smallPrime xs outerU i) × (ZMod (∏i,smallPrime xs outerU i))ˣ) :=
  mixedCongr (small_modulus_eq_root h outerU xs hslots).symm

def rootSmallTest (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu : SmallUnitData D P q outerU xs v)
    (z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ) : ℝ :=
  crtTest (smallPrime xs outerU) hu.coprime (smallRetained xs outerU)
    (fun i=>residueTransform d (smallPrime xs outerU i))
    (smallCoefficients D outerU xs v hu.frequency hu.denominator)
    (rootSmallEquiv h outerU xs hslots z)

theorem rootResidueIndicator_mul_rootSmallTest (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu : SmallUnitData D P q outerU xs v)
    (z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ) :
    rootResidueIndicator h (z.1,z.2) * (rootSmallTest d h outerU xs hslots D P q v hu z : ℂ) =
      rootSmallTest d h outerU xs hslots D P q v hu z := by
  have hg := guardIndicator_mixedCongr (small_modulus_eq_root h outerU xs hslots).symm z
  change _ = rootResidueIndicator h (z.1,z.2) at hg
  rw [←hg]
  exact actual_guardIndicator_mul_crtTest d (smallPrime xs outerU) hu.coprime
    (smallRetained xs outerU) (smallCoefficients D outerU xs v hu.frequency hu.denominator)
    (rootSmallEquiv h outerU xs hslots z)

theorem rootSmallTest_nonneg (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu : SmallUnitData D P q outerU xs v)
    (z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ) :
    0 ≤ rootSmallTest d h outerU xs hslots D P q v hu z := by
  unfold rootSmallTest crtTest
  apply productTest_nonneg

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
