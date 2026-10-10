import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallAverageSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration

def actualRootDraw {l : ℕ} (h : History l) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs)) (D P q : ℕ) (v : ℤ)
    (hu : SmallUnitData D P q outerU xs v) :
    ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ :=
  (rootSmallEquiv h outerU xs hslots).symm ((P:ZMod (∏i,smallPrime xs outerU i)),hu.giantUnit)

theorem rootSmallTest_actualRootDraw (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu : SmallUnitData D P q outerU xs v) :
    rootSmallTest d h outerU xs hslots D P q v hu
      (actualRootDraw h outerU xs hslots D P q v hu) =
        diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs := by
  unfold rootSmallTest actualRootDraw
  rw [Equiv.apply_symm_apply]
  exact (diagonalSmallMultiplier_eq_crtTest d D P q outerU xs v hu).symm

theorem diagonalSmallTerm_eq_rootSmallTest (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l P : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (z : RemainingTerm sources seed V giant l) (h : History l)
    (hslots : h.root.small.Perm
      (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u ++
       assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) z.1.2))
    (hs : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l))
    (hm : remainingTermMass sources seed V giant l z≠0)
    (hA : diagonalCoefficientTerm d sources seed V giant X G bins outside l P u z≠0) :
    let xs := assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) z.1.2
    let us := assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u
    letI := assignedSmallPrimeFacts sources
      (Template.remainder (l+1) (Template.current seed l))
      (Template.extracted (l+1) (Template.current seed l)) z.1.2 u
    ∃ hu : SmallUnitData (outsideProduct outside) P z.1.1.val us xs z.2.val,
      let draw := actualRootDraw h us xs hslots (outsideProduct outside) P z.1.1.val z.2.val hu
      (diagonalSmallTerm d sources seed V giant outside l P u z : ℂ) =
        rootResidueIndicator h (draw.1,draw.2) *
          (rootSmallTest d h us xs hslots (outsideProduct outside) P z.1.1.val z.2.val hu draw : ℂ) := by
  dsimp only
  let := assignedSmallPrimeFacts sources
    (Template.remainder (l+1) (Template.current seed l))
    (Template.extracted (l+1) (Template.current seed l)) z.1.2 u
  let hu := diagonalSmallTerm_unitData d sources seed V giant X G bins outside l P u z hs hm hA
  refine ⟨hu,?_⟩
  rw [rootResidueIndicator_mul_rootSmallTest,rootSmallTest_actualRootDraw]
  rfl

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
