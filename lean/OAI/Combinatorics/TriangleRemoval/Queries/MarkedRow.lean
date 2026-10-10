import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ProgramDemand

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem markedDemand_map_priority {A : Type*} (as : List A)
    (req : A → Bool) (law : A → PMF (Bool × Bool)) (s t : A → ℕ) :
    markedDemand (as.map (fun a => (⟨req a,law a,s a⟩ : MarkedChild))) =
      markedDemand (as.map (fun a => (⟨req a,law a,t a⟩ : MarkedChild))) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,markedDemand,ih]

theorem markedCheck_map_priority {A : Type*} (as : List A)
    (req : A → Bool) (law : A → PMF (Bool × Bool)) (s t : A → ℕ) :
    markedCheck (as.map (fun a => (⟨req a,law a,s a⟩ : MarkedChild))) =
      markedCheck (as.map (fun a => (⟨req a,law a,t a⟩ : MarkedChild))) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons,markedCheck,ih,
      markedDemand_map_priority as req law s t]

section GridKernel
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def actualMarkedRow (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d k : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ) (ω : (ι × τ) → Fin N) : List MarkedChild :=
  ((((gridCandidates H focus parent).toList).map (fun a => (a,ω a))).mergeSort
    (fun a b => a.2.val ≤ b.2.val)).map (fun p =>
      ⟨required (p.1 :: address),
        if p.2.val < k then ExposureTree.fresh (fun _ => PMF.uniformOfFintype (Fin N))
          (markedGridQueryDepth H N required d p.2.val (p.1 :: address)
            ((H p.1.2).erase p.1.1) (some p.1.2))
        else PMF.pure (false,false), p.2.val⟩)

theorem markedGridQueryDepth_kernel (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d k : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ) :
    ExposureTree.fresh (fun _ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required (d+1) k address focus parent) =
    (productPMF (fun _ : ι × τ => PMF.uniformOfFintype (Fin N))).bind
      (fun ω => markedCheck (actualMarkedRow H N required d k address focus parent ω)) := by
  classical
  rw [markedGridQueryDepth,ExposureTree.fresh_bind]
  rw [← ExposureTree.exposeLabeled_table
    (fun _ : τ => PMF.uniformOfFintype (Fin N)) Prod.snd
    (gridCandidates H focus parent).toList (Finset.nodup_toList _)
    (fun _ : ι × τ => PMF.uniformOfFintype (Fin N)) (by intros; rfl)]
  rw [PMF.bind_map]
  congr 1
  funext ω
  dsimp only [Function.comp_def]
  rw [ExposureTree.fresh_checkMarked]
  simp only [List.map_map,Function.comp_def]
  unfold actualMarkedRow
  calc
    _ = markedCheck
        (((((gridCandidates H focus parent).toList).map (fun a => (a,ω a))).mergeSort
          (fun a b => a.2.val ≤ b.2.val)).map (fun p =>
          (⟨required (p.1 :: address),
            if p.2.val < k then ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
              (markedGridQueryDepth H N required d p.2.val (p.1 :: address)
                ((H p.1.2).erase p.1.1) (some p.1.2))
            else PMF.pure (false,false),0⟩ : MarkedChild))) := by
      congr 1
      apply List.map_congr_left
      intro p _
      split <;> rfl
    _ = _ := markedCheck_map_priority _ _ _ _ _

end GridKernel
end SharpTerminalLeave

end

end OAI
