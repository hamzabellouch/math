import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoordinateEquiv

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving
open Finset Classical
lemma unselected_card {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (e : Fin k ↪ ι) :
    Fintype.card (Unselected e) = Fintype.card ι-k := by
  have he := Fintype.card_congr (coordinateEquiv e)
  simp only [Fintype.card_sum,Fintype.card_fin] at he
  omega
end OrdinaryCorrelations.ArithmeticSaving

end

end OAI
