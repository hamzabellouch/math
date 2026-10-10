import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportSourceBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration
open HistorySignedResidues

theorem source_diagonalSmallMultiplier_mul_liftedResidueTest
    (d : Decomposition) (sources : SourceFamily) (T U : List SourceSlot)
    (x : SourceAssignment sources T) (u : SourceAssignment sources U)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hslots : h.root.small.Perm
      (assignedSlots sources U u ++ assignedSlots sources T x))
    (hsource : ∀ i : Fin T.length, (sources (T.get i).origin).AboveFrequency (V l))
    (hx : (assignmentPrior sources T).mass x ≠ 0)
    (P q : ℕ) [NeZero (pairModulus h k outside)] (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (hA : rootModulus h ∣ M) :
    (diagonalSmallMultiplier d (outside.prod * halfProduct P (assignedSlots sources U u))
      h.root.frequency q (assignedSlots sources T x) : ℂ) *
        liftedResidueTest (residueTransform d) V outside h k M hd
          ((P : ZMod M), (q : ZMod M)) =
    (sourceLiftedRootSmallTest d sources T U x u h hs hslots hsource hx M hA
      ((P : ZMod M), (q : ZMod M)) : ℂ) *
        liftedResidueTest (residueTransform d) V outside h k M hd
          ((P : ZMod M), (q : ZMod M)) := by
  let := assignedSmallPrimeFacts sources T U x u
  exact diagonalSmallMultiplier_mul_liftedResidueTest d h k hs ks
    (assignedSlots sources U u) (assignedSlots sources T x) hslots outside.prod
    h.root.giantPlus h.root.giantMinus P q h.root.frequency
    (sourceReferenceSmallUnitData sources T U x u h hs hslots hsource hx) M hd hA

section Actual
variable (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant : PrimeSource) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (z : RemainingTerm sources seed V giant l)
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hslots : h.root.small.Perm
      (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u ++
       assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) z.1.2))
    (hf : h.root.frequency = z.2.val)
    (hsource : ∀ i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources ((Template.remainder (l+1) (Template.current seed l)).get i).origin).AboveFrequency (V l))
    (hx : (assignmentPrior sources (Template.remainder (l+1) (Template.current seed l))).mass z.1.2 ≠ 0)
    [NeZero (pairModulus h k outside)] (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (hA : rootModulus h ∣ M)

theorem diagonalSmallTerm_eq_multiplier (P : ℕ) :
    diagonalSmallTerm d sources seed V giant outside l P u z =
      diagonalSmallMultiplier d
        (outside.prod * halfProduct P
          (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))
        z.2.val z.1.1.val
        (assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) z.1.2) := rfl

include ks hf

theorem diagonalSmallTerm_mul_liftedResidueTest (P : ℕ) :
    (diagonalSmallTerm d sources seed V giant outside l P u z : ℂ) *
      liftedResidueTest (residueTransform d) V outside h k M hd
        ((P : ZMod M), (z.1.1.val : ZMod M)) =
    (sourceLiftedRootSmallTest d sources
      (Template.remainder (l+1) (Template.current seed l))
      (Template.extracted (l+1) (Template.current seed l)) z.1.2 u h hs hslots hsource hx M hA
      ((P : ZMod M), (z.1.1.val : ZMod M)) : ℂ) *
      liftedResidueTest (residueTransform d) V outside h k M hd
        ((P : ZMod M), (z.1.1.val : ZMod M)) := by
  rw [diagonalSmallTerm_eq_multiplier, ← hf]
  exact source_diagonalSmallMultiplier_mul_liftedResidueTest d sources
    (Template.remainder (l+1) (Template.current seed l))
    (Template.extracted (l+1) (Template.current seed l)) z.1.2 u h k hs ks
    hslots hsource hx P z.1.1.val M hd hA

theorem diagonalSmallTerm_int_mul_liftedResidueTest (P : ℤ) (hP : 0 ≤ P) :
    (diagonalSmallTerm d sources seed V giant outside l P.toNat u z : ℂ) *
      liftedResidueTest (residueTransform d) V outside h k M hd
        ((P : ZMod M), (z.1.1.val : ZMod M)) =
    (sourceLiftedRootSmallTest d sources
      (Template.remainder (l+1) (Template.current seed l))
      (Template.extracted (l+1) (Template.current seed l)) z.1.2 u h hs hslots hsource hx M hA
      ((P : ZMod M), (z.1.1.val : ZMod M)) : ℂ) *
      liftedResidueTest (residueTransform d) V outside h k M hd
        ((P : ZMod M), (z.1.1.val : ZMod M)) := by
  have hcast : (P.toNat : ZMod M) = (P : ZMod M) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hP]
  simpa only [hcast] using diagonalSmallTerm_mul_liftedResidueTest d sources seed V giant
    outside l u z h k hs ks hslots hf hsource hx M hd hA P.toNat

end Actual

theorem remainingTerm_smallAssignment_mass_ne_zero
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant : PrimeSource) (l : ℕ) (z : RemainingTerm sources seed V giant l)
    (hm : remainingTermMass sources seed V giant l z ≠ 0) :
    (assignmentPrior sources (Template.remainder (l+1) (Template.current seed l))).mass z.1.2 ≠ 0 :=
  ((remainingPrior_mass_ne_zero_iff sources _ giant z.1).mp hm).2

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
