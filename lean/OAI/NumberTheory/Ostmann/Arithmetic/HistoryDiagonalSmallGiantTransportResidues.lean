import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportExtension
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationCRT
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration
open HistorySignedResidues HistorySignedSupportReduction HistorySignedDecode

theorem rootUnits_of_residueGuarded {l : ℕ} (h : History l)
    (V : ℕ → ℕ) (outside : List ℕ) (Xp Xm : ℤ)
    (hg : ResidueGuarded V outside (rebuild h Xp Xm)) :
    IsUnit (Xp:ZMod (rootModulus h)) ∧ IsUnit (Xm:ZMod (rootModulus h)) := by
  apply (rootSmallUnits_iff_isUnit h Xp Xm).mp
  apply (rootSmallUnits_iff h Xp Xm).mpr
  intro q hq
  have hr := hg.1
  rw [ResidueRootCoprime,rebuild_root] at hr
  exact hr.2 q.value (List.mem_append_left _ (List.mem_map.mpr ⟨q,hq,rfl⟩))

def liftedRootSmallTest (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (M : ℕ)
    (hA : rootModulus h ∣ M) (z : ZMod M × ZMod M) : ℝ :=
  extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ (ringPairReduction hA z)

theorem liftedRootSmallTest_norm_le (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (M : ℕ)
    (hA : rootModulus h ∣ M) (z : ZMod M × ZMod M) :
    ‖(liftedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ M hA z:ℂ)‖ ≤
      (rootModulus h:ℝ) :=
  extendedRootSmallTest_norm_le d h outerU xs hslots D P₀ q₀ v hu₀ _

theorem diagonalSmallMultiplier_mul_liftedResidueTest (d : Decomposition) {l : ℕ}
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v)
    [NeZero (pairModulus h k outside)] (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (hA : rootModulus h ∣ M) :
    (diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs:ℂ) *
      liftedResidueTest (residueTransform d) V outside h k M hd ((P:ZMod M),(q:ZMod M)) =
    (liftedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ M hA
      ((P:ZMod M),(q:ZMod M)):ℂ) *
      liftedResidueTest (residueTransform d) V outside h k M hd ((P:ZMod M),(q:ZMod M)) := by
  classical
  have he := liftedResidueTest_intCast (residueTransform d) h k hs ks M hd (P:ℤ) (q:ℤ)
  simp only [Int.cast_natCast] at he
  rw [he]
  split
  · rename_i hg
    have hu := rootUnits_of_residueGuarded h V outside (P:ℤ) (q:ℤ) hg.1
    simp only [Int.cast_natCast] at hu
    have ht := extendedRootSmallTest_natCast d h outerU xs hslots D P₀ q₀ P q v hu₀ hu.1 hu.2
    have hl : liftedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ M hA
        ((P:ZMod M),(q:ZMod M)) = diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs := by
      simpa only [liftedRootSmallTest,ringPairReduction,map_natCast] using ht
    rw [hl]
  · simp

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
