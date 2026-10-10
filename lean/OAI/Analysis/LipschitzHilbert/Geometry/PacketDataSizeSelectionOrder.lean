import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSizeStopping

namespace OAI

/-! The near-extremal selection rule orders every later failing test.
Monotonicity uses the actual decreasing packet sets, not a separate order assumption. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
open PacketLatticeData
attribute [local instance] Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ} {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_failing
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ T∈tops, P.sizeTestFails negative w cb tau sigma cell grid c initial T := by
  induction h with
  | stop => simp
  | step R T tops remaining hT _ _ ih =>
    intro U hU
    rcases List.mem_cons.mp hU with rfl | hU
    · exact hT
    · exact P.sizeTestFails_mono negative w cb tau sigma cell grid c Finset.sdiff_subset U (ih U hU)

theorem direction_order
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    tops.Pairwise (fun T U => sizeDirection negative T.slope<sizeDirection negative U.slope+epsilon) := by
  induction h with
  | stop => exact List.Pairwise.nil
  | step R T tops remaining _ hfirst htail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro U hU
    exact hfirst U (P.sizeTestFails_mono negative w cb tau sigma cell grid c Finset.sdiff_subset U
      (htail.selected_failing U hU))

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
