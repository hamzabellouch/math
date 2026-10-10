import OAI.Combinatorics.DiscreteConvexity.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union

namespace OAI

/-!
# Finite objects in the elementary covering argument

Sampling is indexed by ordered pairs of edges, including diagonal pairs.
Different pairs remain different indices even if their unions coincide.
Residual generators are indexed by injective ordered tuples.
-/

namespace TalagrandDiscreteConvexity.Covering

variable {V : Type*} [DecidableEq V]

/-- An ordered tuple of distinct members of a finite edge family. -/
def EdgeTuple (H : Family V) (t : ℕ) :=
  {f : Fin t → ↥H // Function.Injective f}

noncomputable instance edgeTupleFintype (H : Family V) (t : ℕ) :
    Fintype (EdgeTuple H t) := by
  classical
  exact Subtype.fintype _

/-- All independent ordered-pair sampling indices. -/
abbrev PairIndex (H : Family V) := ↥H × ↥H

/-- A sampling outcome specifies precisely the pairs selected. -/
abbrev Sample (H : Family V) := Finset (PairIndex H)

def tupleUnion {H : Family V} {t : ℕ} (f : EdgeTuple H t) : Finset V :=
  Finset.univ.biUnion (fun i => (f.val i).val)

noncomputable def tuplePairs {H : Family V} {t : ℕ}
    (f : EdgeTuple H t) : Finset (PairIndex H) := by
  classical
  exact Finset.univ.image (fun ij : Fin t × Fin t => (f.val ij.1, f.val ij.2))

@[simp] theorem mem_tupleUnion {H : Family V} {t : ℕ}
    {f : EdgeTuple H t} {v : V} :
    v ∈ tupleUnion f ↔ ∃ i, v ∈ (f.val i).val := by
  simp [tupleUnion]

@[simp] theorem mem_tuplePairs {H : Family V} {t : ℕ}
    {f : EdgeTuple H t} {p : PairIndex H} :
    p ∈ tuplePairs f ↔ ∃ i j, (f.val i, f.val j) = p := by
  classical
  simp [tuplePairs, Prod.exists]

/-- The weighted number of edges containing a prescribed vertex set. -/
noncomputable def weightedDegree (H : Family V) (rho : ℝ) (r : ℕ)
    (I : Finset V) : ℝ := by
  classical
  exact ((H.filter (fun e => I ⊆ e)).card : ℝ) * rho ^ (r - I.card)

/-- Edges avoiding all prescribed initial generators. -/
noncomputable def regularFamily (H C0 : Family V) : Family V := by
  classical
  exact H.filter (fun e => ∀ I ∈ C0, ¬ I ⊆ e)

@[simp] theorem mem_regularFamily {H C0 : Family V} {e : Finset V} :
    e ∈ regularFamily H C0 ↔ e ∈ H ∧ ∀ I ∈ C0, ¬ I ⊆ e := by
  classical
  simp [regularFamily]

theorem regularFamily_subset (H C0 : Family V) : regularFamily H C0 ⊆ H := by
  intro e he
  exact (mem_regularFamily.mp he).1

section FiniteGround

variable [Fintype V]

/-- The high weighted-degree sets used as the initial generators. -/
noncomputable def initialFamily (H : Family V) (rho : ℝ) (r : ℕ)
    (T : ℝ) : Family V := by
  classical
  exact Finset.univ.filter (fun I => I.card ≤ r ∧ T < weightedDegree H rho r I)

/-- The regular edges for the actual high-degree initial family. -/
noncomputable def regularEdges (H : Family V) (rho : ℝ) (r : ℕ)
    (T : ℝ) : Family V := regularFamily H (initialFamily H rho r T)

/-- Sets containing at least `m` distinct edges of the original family. -/
noncomputable def denseFamily (H : Family V) (m : ℕ) : Family V := by
  classical
  exact Finset.univ.filter (fun S => m ≤ (H.filter (fun e => e ⊆ S)).card)

@[simp] theorem mem_initialFamily {H : Family V} {rho T : ℝ}
    {r : ℕ} {I : Finset V} :
    I ∈ initialFamily H rho r T ↔ I.card ≤ r ∧ T < weightedDegree H rho r I := by
  classical
  simp [initialFamily]

@[simp] theorem mem_regularEdges {H : Family V} {rho T : ℝ}
    {r : ℕ} {e : Finset V} :
    e ∈ regularEdges H rho r T ↔
      e ∈ H ∧ ∀ I ∈ initialFamily H rho r T, ¬ I ⊆ e := by
  exact mem_regularFamily

@[simp] theorem mem_denseFamily {H : Family V} {m : ℕ} {S : Finset V} :
    S ∈ denseFamily H m ↔ m ≤ (H.filter (fun e => e ⊆ S)).card := by
  classical
  simp [denseFamily]

theorem regularEdges_subset (H : Family V) (rho : ℝ) (r : ℕ) (T : ℝ) :
    regularEdges H rho r T ⊆ H := regularFamily_subset _ _

end FiniteGround

end TalagrandDiscreteConvexity.Covering

end OAI
