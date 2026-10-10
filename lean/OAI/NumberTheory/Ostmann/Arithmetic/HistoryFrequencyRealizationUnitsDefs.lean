import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyResidues

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts

def FrequencyUnits (R : ℕ) : {l : ℕ} → History l → Prop
  | _,.leaf a => Nat.Coprime (bulkProduct a.small) R
  | _,.node a _ comp _ _ left right =>
      Nat.Coprime (bulkProduct a.small) R ∧
      Nat.Coprime (comp.map SmallSlot.value).prod R ∧
      FrequencyUnits R left ∧ FrequencyUnits R right

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
