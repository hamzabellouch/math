import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuliBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitDataBasic
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBoundsFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitData
open Construction DiagonalSmallResidueNorm HistoryPairBulkTransport

theorem assigned_root_primeSmall (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) :
    (assignedHistory sources seed V l s gp gm x c).root.PrimeSmall := by
  simpa only [assignedHistory,decodeHistory_root,assignedRoot,State.PrimeSmall] using
    assignedSlots_prime sources (Template.current seed l) x

theorem assigned_smallUnitData (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) (outerU xs : List SmallSlot) (outside : List ℕ)
    (hslots : (assignedHistory sources seed V l s gp gm x c).root.small.Perm (outerU++xs))
    (hx : (assignmentPrior sources (Template.current seed l)).mass x ≠ 0)
    (hsource : ∀origin,(sources origin).AboveFrequency (V l))
    (hs : s ≠ 0) (hsv : s.natAbs ≤ V l)
    (hstatic : ((assignedHistory sources seed V l s gp gm x c).root.small.map
      SmallSlot.value ++ outside).Pairwise Nat.Coprime) :
    SmallUnitData outside.prod 1 1 outerU xs s := by
  have hh := smallUnitData_of_static _ (assigned_root_primeSmall sources seed V l s gp gm x c)
    outerU xs outside hslots hstatic
  simp only [assignedHistory,decodeHistory_root,assignedRoot] at hh
  apply hh hs
  intro i
  have hi : xs[i] ∈ assignedSlots sources (Template.current seed l) x := by
    have hh := hslots.mem_iff.mpr (List.mem_append_right outerU (List.getElem_mem i.isLt))
    simpa only [assignedHistory,decodeHistory_root,assignedRoot,Fin.getElem_fin] using hh
  have hm := assignedSlots_source_mass_ne_zero sources (Template.current seed l) x hx xs[i] hi
  exact hsv.trans_lt (sourceMass_value_gt hsource hm)

end Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitData

end

end OAI
