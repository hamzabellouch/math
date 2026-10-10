import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingIntrinsicProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixTimeExchange

namespace OAI

/-! # The next intrinsic product in any extended-prefix Gaussian chart -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

def nextRootIndex (q : InitialRootStep n) :
    q.NextRoot ≃ ↥(allPositiveRoots n \ insert q.root q.processed) where
  toFun p := ⟨p.val,by simpa only [remaining,initialRemaining_erase] using p.prop⟩
  invFun p := ⟨p.val,by simpa only [remaining,initialRemaining_erase] using p.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nextProduct_map_cast (q : InitialRootStep n)
    {D : Finset (Fin n)} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots n)
    (ν : q.NextRoot → Measure ℝ) [∀ p, SigmaFinite (ν p)] :
    ((Measure.pi ν).map q.nextGroupCoordinates.symm).map q.nextGroupCast =
      (Measure.pi fun p : ↥(allPositiveRoots n \ insert q.root q.processed) =>
        ν (q.nextRootIndex.symm p)).map (c.remainingGroupCoordinates q.next_initial hf).symm := by
  let e := q.nextRootIndex
  let E := MeasurableEquiv.piCongrLeft
    (fun _ : ↥(allPositiveRoots n \ insert q.root q.processed) => ℝ) e
  have hE : MeasurePreserving E (Measure.pi ν)
      (Measure.pi fun p : ↥(allPositiveRoots n \ insert q.root q.processed) => ν (e.symm p)) := by
    simpa only [e.symm_apply_apply] using
      (measurePreserving_piCongrLeft (fun p => ν (e.symm p)) e)
  rw [←hE.map_eq,Measure.map_map q.nextGroupCast.measurable q.nextGroupCoordinates.symm.measurable,
    Measure.map_map (c.remainingGroupCoordinates q.next_initial hf).symm.measurable E.measurable]
  apply congrArg (fun F => (Measure.pi ν).map F)
  funext f
  apply (c.remainingGroupCoordinates q.next_initial hf).injective
  rw [Function.comp_apply,Function.comp_apply,Homeomorph.apply_symm_apply]
  funext p
  rw [c.remainingGroupCoordinates_apply]
  change (q.nextGroupCoordinates.symm f).val.val p.val.1 p.val.2 = f (e.symm p)
  have H := q.nextGroupCoordinates_apply (q.nextGroupCoordinates.symm f) (e.symm p)
  have hp : (e.symm p).val = p.val := rfl
  rw [hp] at H
  simpa only [Homeomorph.apply_symm_apply] using H.symm

theorem ae_nextIntrinsicProduct_chain (d : ℕ) (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ, (q.nextIntrinsicProduct d μ x).map q.nextGroupCast =
      c.remainingIntrinsicProduct q.next_initial hf μ x := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have H (p : q.NextRoot) := ae_intrinsicRootLeaf_spec
    (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ
    ((ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _)
  filter_upwards [ae_all_iff.mpr H] with x hx
  let ν := fun p : q.NextRoot =>
    intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x
  let : ∀ p : q.NextRoot, IsLocallyFiniteMeasure (ν p) := fun p => (hx p).1
  exact q.nextProduct_map_cast c hf ν

end InitialRootStep
end DukePrimeDegree

end

end OAI
