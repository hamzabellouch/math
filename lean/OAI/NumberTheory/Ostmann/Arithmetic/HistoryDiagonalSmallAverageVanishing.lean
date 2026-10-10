import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNorm
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlockDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem exists_nonunit_component [_decidableEqIndex : DecidableEq ι] (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (z : ZMod (∏ i,p i) × (ZMod (∏ i,p i))ˣ) (hz : ¬ IsUnit z.1) :
    ∃i,¬ IsUnit (crtPairEquiv p hcop z i).1 := by
  classical
  by_contra hn
  have hall : ∀i,IsUnit (crtPairEquiv p hcop z i).1 := by simpa using hn
  have hp : IsUnit (ZMod.prodEquivPi p hcop z.1) := by
    apply Pi.isUnit_iff.mpr
    intro i
    exact hall i
  apply hz
  simpa using hp.map (ZMod.prodEquivPi p hcop).symm.toMonoidHom

theorem crtTest_eq_zero_of_not_isUnit (p : ι → ℕ) [∀i,Fact (p i).Prime]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (retained : ι → Bool) (g : ∀i,ZMod (p i) → ℂ) (hg0 : ∀i,g i 0=0)
    (a : ∀i,(ZMod (p i))ˣ)
    (z : ZMod (∏ i,p i) × (ZMod (∏ i,p i))ˣ) (hz : ¬ IsUnit z.1) :
    crtTest p hcop retained g a z=0 := by
  classical
  obtain ⟨i,hi⟩ := exists_nonunit_component p hcop z hz
  have hzero : (crtPairEquiv p hcop z i).1=0 := by
    simpa only [isUnit_iff_ne_zero,not_not] using hi
  unfold crtTest productTest
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [localFactor,transformFactor,unitFactor,hzero,hg0]

theorem guardIndicator_mul_crtTest (p : ι → ℕ) [∀i,Fact (p i).Prime]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (retained : ι → Bool) (g : ∀i,ZMod (p i) → ℂ) (hg0 : ∀i,g i 0=0)
    (a : ∀i,(ZMod (p i))ˣ)
    (z : ZMod (∏ i,p i) × (ZMod (∏ i,p i))ˣ) :
    guardIndicator (IsUnit z.1 ∧ IsUnit (z.2 : ZMod (∏ i,p i))) *
      (crtTest p hcop retained g a z : ℂ) = crtTest p hcop retained g a z := by
  classical
  by_cases hz : IsUnit z.1
  · simp [guardIndicator,hz]
  · rw [crtTest_eq_zero_of_not_isUnit p hcop retained g hg0 a z hz]
    simp

theorem actual_guardIndicator_mul_crtTest (d : Decomposition)
    (p : ι → ℕ) [∀i,Fact (p i).Prime]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (retained : ι → Bool) (a : ∀i,(ZMod (p i))ˣ)
    (z : ZMod (∏ i,p i) × (ZMod (∏ i,p i))ˣ) :
    guardIndicator (IsUnit z.1 ∧ IsUnit (z.2 : ZMod (∏ i,p i))) *
      (crtTest p hcop retained (fun i=>residueTransform d (p i)) a z : ℂ) =
        crtTest p hcop retained (fun i=>residueTransform d (p i)) a z :=
  guardIndicator_mul_crtTest p hcop retained _
    (fun i => by simp [residueTransform_eq,Supply.additiveTransform_zero]) a z

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
