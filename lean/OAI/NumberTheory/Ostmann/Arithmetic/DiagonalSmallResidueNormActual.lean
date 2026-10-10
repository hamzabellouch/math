import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormActualCRT
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open Construction
open scoped BigOperators

theorem assignedSmallPrimeFacts (sources : SourceFamily) (T U : List SourceSlot)
    (x : SourceAssignment sources T) (u : SourceAssignment sources U) :
    ∀ i, Fact (smallPrime (assignedSlots sources T x) (assignedSlots sources U u) i).Prime := by
  intro i
  constructor
  cases i with
  | inl i => exact assignedSlots_prime sources T x _ (List.getElem_mem i.isLt)
  | inr i => exact assignedSlots_prime sources U u _ (List.getElem_mem i.isLt)

section
variable (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant : PrimeSource) (X G : ℝ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (l P : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (z : RemainingTerm sources seed V giant l)

theorem diagonalSmallTerm_unitData
    (hs : ∀ i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l))
    (hm : remainingTermMass sources seed V giant l z ≠ 0)
    (hA : diagonalCoefficientTerm d sources seed V giant X G bins outside l P u z ≠ 0) :
    SmallUnitData (outsideProduct outside) P z.1.1.val
      (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u)
      (assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) z.1.2) z.2.val := by
  let T := Template.remainder (l+1) (Template.current seed l)
  let U := Template.extracted (l+1) (Template.current seed l)
  let xs := assignedSlots sources T z.1.2
  let us := assignedSlots sources U u
  let := assignedSmallPrimeFacts sources T U z.1.2 u
  have hroot := actualCoefficient_root_support sources seed V X G (residueTransform d) bins outside l
    (remainingState sources (Template.current seed l) (l+1) giant P u z.1 z.2.val) hA
  apply smallUnitData_of_state
    (remainingState sources (Template.current seed l) (l+1) giant P u z.1 z.2.val)
    us xs outside
    (Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _))
    hroot.2.2.2.1 hroot.2.2.2.2.1
  intro i
  have hx : (assignmentPrior sources T).mass z.1.2 ≠ 0 :=
    ((remainingPrior_mass_ne_zero_iff sources T giant z.1).mp hm).2
  have hi : xs[i] ∈ assignedSlots sources T z.1.2 := List.getElem_mem i.isLt
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
  have hlarge : V l < xs[i].value := by
    rw [← hj]
    exact hs j (z.1.2 j) (assignmentPrior_component_mass_ne_zero sources T z.1.2 hx j)
  exact hroot.2.2.2.2.2.trans_lt hlarge

theorem diagonalSmallTerm_eq_actual_crtTest
    (hs : ∀ i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l))
    (hm : remainingTermMass sources seed V giant l z ≠ 0)
    (hA : diagonalCoefficientTerm d sources seed V giant X G bins outside l P u z ≠ 0) :
    let T := Template.remainder (l+1) (Template.current seed l)
    let U := Template.extracted (l+1) (Template.current seed l)
    let xs := assignedSlots sources T z.1.2
    let us := assignedSlots sources U u
    letI := assignedSmallPrimeFacts sources T U z.1.2 u
    ∃ h : SmallUnitData (outsideProduct outside) P z.1.1.val us xs z.2.val,
      diagonalSmallTerm d sources seed V giant outside l P u z =
        crtTest (smallPrime xs us) h.coprime (smallRetained xs us)
          (fun i => residueTransform d (smallPrime xs us i))
          (smallCoefficients (outsideProduct outside) us xs z.2.val h.frequency h.denominator)
          ((P : ZMod (∏ i, smallPrime xs us i)), h.giantUnit) := by
  dsimp only
  let := assignedSmallPrimeFacts sources
    (Template.remainder (l+1) (Template.current seed l))
    (Template.extracted (l+1) (Template.current seed l)) z.1.2 u
  refine ⟨diagonalSmallTerm_unitData d sources seed V giant X G bins outside l P u z hs hm hA, ?_⟩
  exact diagonalSmallMultiplier_eq_crtTest d _ _ _ _ _ _ _

end
end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
