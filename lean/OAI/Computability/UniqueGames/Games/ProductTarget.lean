import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Digits.Lemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas
import OAI.Computability.UniqueGames.Machines.MachineBinaryInputReductionLemmas

namespace OAI

/-!
Explicit numbered permutation-table outputs for bipartite graphs and products.
All numbering maps are supplied as actual equivalences; the product uses the
computable radix equivalence with division/remainder inverse, never an arbitrary
finite-type enumeration. The value bridge preserves every list occurrence.
-/

namespace UniqueGamesTheorem.Explicit.ProductTarget

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

/-- Full forward and inverse tables of an explicit finite permutation. -/
def fullTable (p : Equiv.Perm (Fin q)) : PermutationTable q where
  images := Vector.ofFn p
  inverseImages := Vector.ofFn p.symm
  leftInverse a := by simp
  rightInverse a := by simp

@[simp] theorem fullTable_images (p : Equiv.Perm (Fin q)) (a : Fin q) :
    (fullTable p).images[a] = p a := by simp [fullTable]

@[simp] theorem permutationEquiv_fullTable (p : Equiv.Perm (Fin q)) :
    permutationEquiv (fullTable p) = p := by
  ext a
  simp [permutationEquiv, fullTable]

/-- One explicitly addressed row, with a separately supplied complete table. -/
def row (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ≃ Fin N)
    (edges : Fin M ≃ E) (tables : E → PermutationTable q) (i : Fin M) :
    Constraint N q where
  source := vertices (Sum.inl (G.left (edges i)))
  target := vertices (Sum.inr (G.right (edges i)))
  permutation := tables (edges i)

def render (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ≃ Fin N)
    (edges : Fin M ≃ E) (tables : E → PermutationTable q) (hM : 0 < M) :
    Instance q where
  vertices := N
  constraints := List.ofFn (row G vertices edges tables)
  nonempty := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [List.length_ofFn, List.length_nil] at hlength
    omega

@[simp] theorem render_length (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    (render G vertices edges tables hM).constraints.length = M := by
  simp [render]

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (i : Fin (render G vertices edges tables hM).constraints.length) :
    (render G vertices edges tables hM).constraints[i] =
      row G vertices edges tables ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges tables))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def render_simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    SimpleBipartite (render G vertices edges tables hM) where
  side v := Sum.elim (fun _ => false) (fun _ => true) (vertices.symm v)
  sourceSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inl]
  targetSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inr]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges tables ⟨i.val, hi⟩).source,
          (row G vertices edges tables ⟨i.val, hi⟩).target) =
        ((row G vertices edges tables ⟨j.val, hj⟩).source,
          (row G vertices edges tables ⟨j.val, hj⟩).target) := by
      simpa only [render_get] using! hij
    have hedge : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective hedge))

section Value

variable [Fintype E]

/-- A full vertex labeling pulls back to two independently local labelings. -/
theorem render_count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges tables hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  have ht (e : E) (a : Fin q) : (tables e).images[a] = G.permutation e a :=
    congrArg (fun p : Equiv.Perm (Fin q) => p a) (htable e)
  change countSatisfied labeling (List.ofFn (row G vertices edges tables)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, ht]

def mergeLabelings (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) : Fin N → Fin q :=
  fun v => Sum.elim left right (vertices.symm v)

@[simp] theorem mergeLabelings_left (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) (x : L) :
    mergeLabelings vertices left right (vertices (Sum.inl x)) = left x := by
  simp [mergeLabelings]

@[simp] theorem mergeLabelings_right (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) (y : R) :
    mergeLabelings vertices left right (vertices (Sum.inr y)) = right y := by
  simp [mergeLabelings]

theorem render_count_merge (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (left : L → Fin q) (right : R → Fin q) :
    countSatisfied (mergeLabelings vertices left right)
      (render G vertices edges tables hM).constraints = G.satisfiedCount left right := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    render_count G vertices edges tables hM htable (mergeLabelings vertices left right)

variable [Fintype L] [Fintype R]

theorem render_maxSatisfied (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges tables hM) =
      G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    erw [render_count G vertices edges tables hM htable]
    exact G.satisfiedCount_le_maxSatisfied _ _
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← render_count_merge G vertices edges tables hM htable]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges tables hM) (mergeLabelings vertices labeling.1 labeling.2)

theorem render_value (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.value (render G vertices edges tables hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [render_maxSatisfied G vertices edges tables hM htable, render_length]
  have hcard : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hcard]

end Value

/-- The product order is increasing radix address, with coordinate zero the
least significant digit. The inverse computes each digit by division/modulo. -/
def tuples (n t : ℕ) : List (Fin t → Fin n) :=
  (List.finRange (n ^ t)).map finFunctionFinEquiv.symm

@[simp] theorem tuples_length (n t : ℕ) : (tuples n t).length = n ^ t := by
  simp [tuples]

theorem tuples_mem {n t : ℕ} (f : Fin t → Fin n) : f ∈ tuples n t := by
  apply List.mem_map.mpr
  exact ⟨finFunctionFinEquiv f, List.mem_finRange _, Equiv.symm_apply_apply _ _⟩

theorem tuples_nodup (n t : ℕ) : (tuples n t).Nodup :=
  (List.nodup_finRange _).map finFunctionFinEquiv.symm.injective

@[simp] theorem tuples_get (n t : ℕ) (i : Fin (n ^ t)) :
    (tuples n t)[i.val]'(by simpa only [tuples_length] using i.isLt) =
      finFunctionFinEquiv.symm i := by
  simp [tuples]

theorem tuple_address (n t : ℕ) (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin t, (f i : ℕ) * n ^ (i : ℕ) :=
  finFunctionFinEquiv_apply f

/-- The explicit address and `ofDigits` share the same least-significant-first
coordinate order, with no restriction on the radix beyond the digit type. -/
theorem address_eq_ofDigits {n t : ℕ} (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) = Nat.ofDigits n (List.ofFn (fun i => (f i : ℕ))) := by
  have hmap :
      (List.ofFn (fun i => (f i : ℕ))).mapIdx (fun i a => a * n ^ i) =
        List.ofFn (fun i : Fin t => (f i : ℕ) * n ^ (i : ℕ)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [finFunctionFinEquiv_apply, Nat.ofDigits_eq_sum_mapIdx, hmap, List.sum_ofFn]

/-- A forward Horner controller reads the coordinate words in reverse order.
This is a word-order identity, separate from its machine execution theorem. -/
theorem address_eq_horner {n t : ℕ} (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) =
      (List.ofFn (fun i => (f i : ℕ))).reverse.foldl
        (fun acc digit => n * acc + digit) 0 := by
  rw [address_eq_ofDigits, Nat.ofDigits_eq_foldr, List.foldl_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

end UniqueGamesTheorem.Explicit.ProductTarget

end OAI
