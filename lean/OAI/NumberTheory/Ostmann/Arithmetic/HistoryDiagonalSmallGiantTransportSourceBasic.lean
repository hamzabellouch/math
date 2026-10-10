import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportResidues

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration

theorem assignedSmall_aboveFrequency (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) (N : ℕ)
    (hsource : ∀ i : Fin T.length, (sources (T.get i).origin).AboveFrequency N)
    (hx : (assignmentPrior sources T).mass x ≠ 0) :
    ∀ i : Fin (assignedSlots sources T x).length,
      N < (assignedSlots sources T x)[i].value := by
  intro i
  have hi : (assignedSlots sources T x)[i] ∈ assignedSlots sources T x :=
    List.getElem_mem i.isLt
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hi
  rw [← hj]
  exact hsource j (x j) (assignmentPrior_component_mass_ne_zero sources T x hx j)

theorem sourceReferenceSmallUnitData (sources : SourceFamily) (T U : List SourceSlot)
    (x : SourceAssignment sources T) (u : SourceAssignment sources U)
    {l : ℕ} (h : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside)
    (hslots : h.root.small.Perm
      (assignedSlots sources U u ++ assignedSlots sources T x))
    (hsource : ∀ i : Fin T.length, (sources (T.get i).origin).AboveFrequency (V l))
    (hx : (assignmentPrior sources T).mass x ≠ 0) :
    SmallUnitData outside.prod h.root.giantPlus h.root.giantMinus
      (assignedSlots sources U u) (assignedSlots sources T x) h.root.frequency := by
  let := assignedSmallPrimeFacts sources T U x u
  exact supportedSmallUnitData h hs (assignedSlots sources U u)
    (assignedSlots sources T x) hslots
    (assignedSmall_aboveFrequency sources T x (V l) hsource hx)

def sourceLiftedRootSmallTest (d : Decomposition) (sources : SourceFamily)
    (T U : List SourceSlot) (x : SourceAssignment sources T)
    (u : SourceAssignment sources U) {l : ℕ} (h : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (hslots : h.root.small.Perm
      (assignedSlots sources U u ++ assignedSlots sources T x))
    (hsource : ∀ i : Fin T.length, (sources (T.get i).origin).AboveFrequency (V l))
    (hx : (assignmentPrior sources T).mass x ≠ 0)
    (M : ℕ) (hA : rootModulus h ∣ M) (z : ZMod M × ZMod M) : ℝ := by
  let := assignedSmallPrimeFacts sources T U x u
  exact liftedRootSmallTest d h (assignedSlots sources U u) (assignedSlots sources T x)
    hslots outside.prod h.root.giantPlus h.root.giantMinus h.root.frequency
    (sourceReferenceSmallUnitData sources T U x u h hs hslots hsource hx) M hA z

theorem sourceLiftedRootSmallTest_norm_le (d : Decomposition) (sources : SourceFamily)
    (T U : List SourceSlot) (x : SourceAssignment sources T)
    (u : SourceAssignment sources U) {l : ℕ} (h : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (hslots : h.root.small.Perm
      (assignedSlots sources U u ++ assignedSlots sources T x))
    (hsource : ∀ i : Fin T.length, (sources (T.get i).origin).AboveFrequency (V l))
    (hx : (assignmentPrior sources T).mass x ≠ 0)
    (M : ℕ) (hA : rootModulus h ∣ M) (z : ZMod M × ZMod M) :
    ‖(sourceLiftedRootSmallTest d sources T U x u h hs hslots hsource hx M hA z : ℂ)‖
      ≤ (rootModulus h : ℝ) := by
  let := assignedSmallPrimeFacts sources T U x u
  exact liftedRootSmallTest_norm_le d h (assignedSlots sources U u)
    (assignedSlots sources T x) hslots outside.prod h.root.giantPlus h.root.giantMinus
    h.root.frequency (sourceReferenceSmallUnitData sources T U x u h hs hslots hsource hx)
    M hA z

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
