import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.MapOutput
import OAI.Combinatorics.TriangleRemoval.Queries.MarkedChild

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
namespace ExposureTree
variable {K V O A : Type*}

def programDemand : List (Bool × ExposureTree K V (Bool × Bool)) → Bool
  | [] => false
  | a :: as => a.1 || programDemand as

def checkMarked : List (Bool × ExposureTree K V (Bool × Bool)) →
    ExposureTree K V (Bool × Bool)
  | [] => .done (true,true)
  | a :: as => bind a.2 (fun z =>
      if z.1 then .done (false, ((!a.1) || z.2) && !programDemand as)
      else mapOutput (fun y => (y.1, ((!a.1) || z.2) && y.2)) (checkMarked as))

@[simp] theorem programDemand_law (ν : K → PMF V)
    (as : List (Bool × ExposureTree K V (Bool × Bool))) :
    markedDemand (as.map (fun a => (⟨a.1,fresh ν a.2,0⟩ : MarkedChild))) =
      programDemand as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,markedDemand,programDemand,ih]

theorem fresh_checkMarked (ν : K → PMF V)
    (as : List (Bool × ExposureTree K V (Bool × Bool))) :
    fresh ν (checkMarked as) =
      markedCheck (as.map (fun a => (⟨a.1,fresh ν a.2,0⟩ : MarkedChild))) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [checkMarked,fresh_bind,List.map_cons,markedCheck]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true,↓reduceIte,fresh,fresh_mapOutput,
      ih,programDemand_law]

theorem checkMarked_outcome
    (as : List (Bool × ExposureTree K V (Bool × Bool))) :
    mapOutput Prod.fst (checkMarked as) =
      checkNone (as.map (fun a => mapOutput Prod.fst a.2)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [checkMarked,mapOutput_bind,List.map_cons,checkNone,bind_mapOutput]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true,↓reduceIte,mapOutput_done,mapOutput_comp]
    exact ih

theorem exposeLabeled_table [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    (ν : K → PMF V) (key : A → K) (as : List A) (ha : as.Nodup)
    (ρ : A → PMF V) (hρ : ∀ a ∈ as, ρ a = ν (key a)) :
    (productPMF ρ).map (fun ω => as.map (fun a => (a,ω a))) =
      fresh ν (exposeLabeled key as) := by
  induction as generalizing ρ with
  | nil => exact PMF.map_const (productPMF ρ) []
  | cons a as ih =>
    obtain ⟨hna,hn⟩ := List.nodup_cons.mp ha
    rw [productPMF_split ρ a,PMF.map_bind,hρ a (List.mem_cons_self)]
    simp only [exposeLabeled,fresh,fresh_bind]
    congr 1
    funext v
    have hx : (productPMF (Function.update ρ a (PMF.pure v))).map
        (fun ω => (a,ω a) :: as.map (fun b => (b,ω b))) =
        (productPMF (Function.update ρ a (PMF.pure v))).map
        (fun ω => (a,v) :: as.map (fun b => (b,ω b))) := by
      apply pmf_bind_congr_on_support
      intro ω hω
      have hw := (productPMF_support _ ω).mp hω a
      have hv : ω a = v := by simpa using hw
      dsimp only [Function.comp_def]
      rw [hv]
    change (productPMF (Function.update ρ a (PMF.pure v))).map
      (fun ω => (a,ω a) :: as.map (fun b => (b,ω b))) = _
    rw [hx]
    have hh := ih hn (Function.update ρ a (PMF.pure v)) (by
      intro b hb
      have hba : b ≠ a := fun he => hna (he ▸ hb)
      rw [Function.update_of_ne hba]
      exact hρ b (List.mem_cons_of_mem _ hb))
    change (productPMF (Function.update ρ a (PMF.pure v))).map
      ((fun xs => (a,v) :: xs) ∘ (fun ω => as.map (fun b => (b,ω b)))) = _
    rw [← PMF.map_comp,hh]
    rfl

end ExposureTree

section MarkedGrid
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def markedGridQueryDepth (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) :
    ℕ → ℕ → List (ι × τ) → Finset ι → Option τ → ExposureTree τ (Fin N) (Bool × Bool)
  | 0, _, _, focus, parent => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList)
      (fun _ => .done (true,true))
  | d+1, k, address, focus, parent => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList)
      (fun values => ExposureTree.checkMarked
        ((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
          (fun p => (required (p.1 :: address), if p.2.val < k then
            markedGridQueryDepth H N required d p.2.val (p.1 :: address)
              ((H p.1.2).erase p.1.1) (some p.1.2)
            else .done (false,false)))))

theorem markedGridQueryDepth_outcome (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ) :
    ExposureTree.mapOutput Prod.fst
      (markedGridQueryDepth H N required d k address focus parent) =
      gridQueryDepth H N d k focus parent := by
  induction d generalizing k address focus parent with
  | zero => simp only [markedGridQueryDepth,gridQueryDepth,ExposureTree.mapOutput_bind,
      ExposureTree.mapOutput_done]
  | succ d ih =>
    simp only [markedGridQueryDepth,gridQueryDepth,ExposureTree.mapOutput_bind]
    congr 1
    funext values
    rw [ExposureTree.checkMarked_outcome,List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    dsimp only [Function.comp_def]
    split
    · exact ih _ _ _ _
    · rfl

end MarkedGrid
end SharpTerminalLeave

end

end OAI
