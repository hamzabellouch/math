import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportSource

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction HistorySignedResidueFactorization HistoryCRTIntegration HistorySignedResidues

abbrev remainingReferenceHistory (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant : PrimeSource) (l P₀ : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (q₀ : giant.Sample)
    (x : SourceAssignment sources (Template.remainder (l+1) (Template.current seed l)))
    (v : ℤ) (c : HistoryChoices sources seed V l) : History l :=
  decodeHistory sources seed V l
    (remainingState sources (Template.current seed l) (l+1) giant P₀ u (q₀,x) v) c

@[simp] theorem remainingReferenceHistory_frequency
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant : PrimeSource) (l P₀ : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (q₀ : giant.Sample)
    (x : SourceAssignment sources (Template.remainder (l+1) (Template.current seed l)))
    (v : ℤ) (c : HistoryChoices sources seed V l) :
    (remainingReferenceHistory sources seed V giant l P₀ u q₀ x v c).root.frequency = v := by
  simp only [remainingReferenceHistory, decodeHistory_root, remainingState]

theorem remainingReferenceHistory_small_perm
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant : PrimeSource) (l P₀ : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (q₀ : giant.Sample)
    (x : SourceAssignment sources (Template.remainder (l+1) (Template.current seed l)))
    (v : ℤ) (c : HistoryChoices sources seed V l) :
    (remainingReferenceHistory sources seed V giant l P₀ u q₀ x v c).root.small.Perm
      (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u ++
       assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) x) := by
  simp only [remainingReferenceHistory, decodeHistory_root, remainingState]
  exact Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)

theorem decoded_diagonalSmallTerm_int_mul_liftedResidueTest
    (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant : PrimeSource) (outside : List ℕ) (l P₀ : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (z : RemainingTerm sources seed V giant l) (q₀ : giant.Sample)
    (c : HistoryChoices sources seed V l) (k : History l)
    (hs : (remainingReferenceHistory sources seed V giant l P₀ u q₀ z.1.2 z.2.val c).Supported V outside)
    (ks : k.Supported V outside)
    (hsource : ∀ i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources ((Template.remainder (l+1) (Template.current seed l)).get i).origin).AboveFrequency (V l))
    (hx : (assignmentPrior sources (Template.remainder (l+1) (Template.current seed l))).mass z.1.2 ≠ 0)
    [NeZero (pairModulus (remainingReferenceHistory sources seed V giant l P₀ u q₀ z.1.2 z.2.val c) k outside)]
    (M : ℕ)
    (hd : pairModulus (remainingReferenceHistory sources seed V giant l P₀ u q₀ z.1.2 z.2.val c) k outside ∣ M)
    (hA : rootModulus (remainingReferenceHistory sources seed V giant l P₀ u q₀ z.1.2 z.2.val c) ∣ M)
    (P : ℤ) (hP : 0 ≤ P) :
    let h := remainingReferenceHistory sources seed V giant l P₀ u q₀ z.1.2 z.2.val c
    let hslots := remainingReferenceHistory_small_perm sources seed V giant l P₀ u q₀ z.1.2 z.2.val c
    (diagonalSmallTerm d sources seed V giant outside l P.toNat u z : ℂ) *
      liftedResidueTest (residueTransform d) V outside h k M hd
        ((P : ZMod M), (z.1.1.val : ZMod M)) =
    (sourceLiftedRootSmallTest d sources
      (Template.remainder (l+1) (Template.current seed l))
      (Template.extracted (l+1) (Template.current seed l)) z.1.2 u h hs hslots hsource hx M hA
      ((P : ZMod M), (z.1.1.val : ZMod M)) : ℂ) *
      liftedResidueTest (residueTransform d) V outside h k M hd
        ((P : ZMod M), (z.1.1.val : ZMod M)) := by
  dsimp only
  exact diagonalSmallTerm_int_mul_liftedResidueTest d sources seed V giant outside l u z
    (remainingReferenceHistory sources seed V giant l P₀ u q₀ z.1.2 z.2.val c) k hs ks
    (remainingReferenceHistory_small_perm sources seed V giant l P₀ u q₀ z.1.2 z.2.val c)
    (remainingReferenceHistory_frequency sources seed V giant l P₀ u q₀ z.1.2 z.2.val c)
    hsource hx M hd hA P hP

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
