import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencySplit
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionArithmetic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistorySignedDecode HistorySignedSupportReduction

def CurrentGiantUnits : {l : ℕ} → SignedHistory l → Prop
  | _,.leaf a =>
    IsUnit (a.giantPlus:ZMod a.frequency.natAbs) ∧
      IsUnit (a.giantMinus:ZMod a.frequency.natAbs)
  | _,.node a _ _ _ _ left right =>
    (IsUnit (a.giantPlus:ZMod a.frequency.natAbs) ∧
      IsUnit (a.giantMinus:ZMod a.frequency.natAbs)) ∧
      CurrentGiantUnits left ∧ CurrentGiantUnits right

theorem rootGiantUnits_of_rootArithmetic (V : ℕ → ℕ) {l : ℕ}
    (h : SignedHistory l) (ha : RootArithmetic V h) :
    IsUnit (h.root.giantPlus:ZMod h.root.frequency.natAbs) ∧
      IsUnit (h.root.giantMinus:ZMod h.root.frequency.natAbs) := by
  have hmem : h.root.frequency ∈ frequencies h := by
    cases h <;> exact List.mem_cons_self
  have hg := ha.2.2.2.2 h.root.frequency hmem
  constructor
  · rw [ZMod.coe_int_isUnit_iff_isCoprime,Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast]
    exact hg.1.symm
  · rw [ZMod.coe_int_isUnit_iff_isCoprime,Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast]
    exact hg.2.symm

theorem currentGiantUnits_of_arithmeticGuards (V : ℕ → ℕ) (outside : List ℕ)
    {l : ℕ} (h : SignedHistory l) (ha : ArithmeticGuards V outside h) :
    CurrentGiantUnits h := by
  induction h with
  | leaf a =>
    rw [ArithmeticGuards] at ha
    exact rootGiantUnits_of_rootArithmetic V (.leaf a) ha.1
  | node a p u hp hm left right ihl ihr =>
    rw [ArithmeticGuards] at ha
    exact ⟨rootGiantUnits_of_rootArithmetic V (.node a p u hp hm left right) ha.1,
      ihl ha.2.2.1,ihr ha.2.2.2⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
