import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalTaperData
import OAI.Combinatorics.KMedian.Sparse.SparseHistories
import OAI.Combinatorics.KMedian.Rounding.RationalRoundEvents
import OAI.Combinatorics.KMedian.Rounding.RationalCopyTransition
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedGraph

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

@[instance_reducible] def copyOrder : LinearOrder (CopyState.Copy (F := F) Δ) :=
  { LinearOrder.lift' (fun p : CopyState.Copy (F := F) Δ => toLex p) (fun _ _ h => h) with
    toDecidableEq := inferInstanceAs (DecidableEq (F × Fin Δ))
    compare := fun a b => if toLex a < toLex b then Ordering.lt else if a=b then Ordering.eq else Ordering.gt
    compare_eq_compareOfLessAndEq := by intros; rfl }

local instance : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

def own (A : Finset (CopyState.Copy (F := F) Δ)) (i : A) : Finset A :=
  univ.filter (fun h => h.val.1=i.val.1)

def enumeration (A : Finset (CopyState.Copy (F := F) Δ)) : Fin A.card ≃ A :=
  (Fintype.orderIsoFinOfCardEq A (Fintype.card_coe A)).toEquiv

def graphLaw (d : F → F → ℚ) (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ)) :
    SparseIntegerLaw (A → Finset A) :=
  SparseEnumeratedGraph.law (enumeration A)
    (fun h i => Taper.sourceMarginals g P (fun a : A => d i.val.1 a.val.1) (own A i) Δ h)

abbrev Payload (F : Type) [LinearOrder F] (Δ : ℕ) (g β : ℚ) :=
  (A : Finset (CopyState.Copy (F := F) Δ)) × RationalBatchData.Event A g β

abbrev State (F : Type) [LinearOrder F] (Δ : ℕ) (g β : ℚ) :=
  Finset (CopyState.Copy (F := F) Δ) × Option (Payload F Δ g β)

def updateEvent (g β : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (e : RationalBatchData.Event A g β) : State F Δ g β := by
  obtain ⟨G,Z⟩ := e
  exact (RationalBatchData.transition A G
    (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z,
    some ⟨A,⟨G,Z⟩⟩)

def step (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) : SparseIntegerLaw (State F Δ g β) :=
  (RationalBatchData.events (graphLaw d g P s.1) Δ g β p φ hp hφ hupper).map
    (updateEvent g β s.1)

omit [Fintype F] in

theorem step_expectation (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (V : State F Δ g β → ℝ) :
    (step d g β p φ P hp hφ hupper s).expectation V=
      (graphLaw d g P s.1).expectation (fun G =>
        (RationalBatchData.proposal G Δ g β p φ hp hφ hupper
          (RationalBatchData.enumeration (RationalBatchData.graph G)
            (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))).expectation
          (fun Z => V (updateEvent g β s.1 ⟨G,Z⟩))) := by
  exact (SparseIntegerLaw.expectation_map
    (RationalBatchData.events (graphLaw d g P s.1) Δ g β p φ hp hφ hupper)
    (updateEvent g β s.1) V).trans
      (RationalBatchData.events_expectation (graphLaw d g P s.1) Δ g β p φ hp hφ hupper
        (fun e => V (updateEvent g β s.1 e)))

omit [Fintype F] in

theorem step_records (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (i : Fin (step d g β p φ P hp hφ hupper s).length) :
    ∃ e : RationalBatchData.Event s.1 g β,
      (step d g β p φ P hp hφ hupper s).states[i.val]=updateEvent g β s.1 e := by
  exact ⟨_, SparseIntegerLaw.map_states _ _ i⟩

def branching (N : ℕ) : ℕ :=
  (N*N+(N*N)*(N*N)+1)*(2*((N+N^2+1)^4+1))

omit [Fintype F] in
theorem step_length (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) : (step d g β p φ P hp hφ hupper s).length ≤ branching s.1.card := by
  apply (RationalBatchData.events_length (graphLaw d g P s.1) Δ g β p φ hp hφ hupper).trans
  change (graphLaw d g P s.1).length * _ ≤ _
  have h := SparseEnumeratedGraph.length_unconditional (enumeration s.1)
    (fun h i => Taper.sourceMarginals g P (fun a : s.1 => d i.val.1 a.val.1) (own s.1 i) Δ h)
  simpa only [branching,Fintype.card_coe,graphLaw] using Nat.mul_le_mul_right
    (2*((s.1.card+s.1.card^2+1)^4+1)) h

theorem branching_mono {N M : ℕ} (h : N ≤ M) : branching N ≤ branching M := by
  unfold branching
  gcongr

theorem step_length_global (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) : (step d g β p φ P hp hφ hupper s).length ≤
      branching (Fintype.card F*Δ) := by
  apply (step_length d g β p φ P hp hφ hupper s).trans
  apply branching_mono
  have hh := card_le_univ s.1
  simpa only [CopyState.Copy,Fintype.card_prod,Fintype.card_fin] using hh

def histories (d : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ) :
    SparseIntegerLaw (SparseHistories.History (State F Δ g β)) :=
  SparseHistories.tree (fun t => step d g β p φ (P t) hp hφ hupper) (A,none) T

theorem histories_length (d : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ) :
    (histories d g β p φ P hp hφ hupper A T).length ≤ (branching (Fintype.card F*Δ))^T := by
  exact SparseHistories.tree_length _ _ _
    (fun t s => step_length_global d g β p φ (P t) hp hφ hupper s) T

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
