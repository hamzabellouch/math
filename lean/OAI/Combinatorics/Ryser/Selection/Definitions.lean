import OAI.Combinatorics.Ryser.Geometry.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

structure Data (F : Type*) [Field F] (n : ℕ) where
  W : Fin n → Finset (Point F)
  dirs : Fin n → Finset (Direction F)

abbrev Position (n K : ℕ) := Fin n × Fin K
abbrev Pool (F : Type*) (n K : ℕ) := Position n K → Point F

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F] {n K : ℕ}

def Conflict (data : Data F n) (i j : Fin n) (b b' : Point F) : Prop :=
  ∃ u ∈ data.W i, ∃ v ∈ data.W j, ∃ d ∈ data.dirs i ∪ data.dirs j,
    projection d ((b + u) - (b' + v)) = 0

theorem projection_sub_eq (d : Direction F) (p q : Point F) :
    projection d (p - q) = projection d p - projection d q := let _ := instDecidableEqF; by
  exact RyserCoveringCounterexample.projection_sub d p q

theorem projection_add_eq (d : Direction F) (p q : Point F) :
    projection d (p + q) = projection d p + projection d q := let _ := instDecidableEqF; by
  exact RyserCoveringCounterexample.projection_add d p q

theorem conflict_iff_forbidden (data : Data F n) (i j : Fin n) (b b' : Point F) :
    Conflict data i j b b' ↔
      ∃ u ∈ data.W i, ∃ v ∈ data.W j, ∃ d ∈ data.dirs i ∪ data.dirs j,
        projection d b = projection d b' + projection d (v - u) := by
  unfold Conflict
  constructor
  · rintro ⟨u, hu, v, hv, d, hd, h⟩
    refine ⟨u, hu, v, hv, d, hd, ?_⟩
    rw [projection_sub_eq, projection_add_eq, projection_add_eq] at h
    rw [projection_sub_eq, ← add_sub_assoc]
    exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp h)
  · rintro ⟨u, hu, v, hv, d, hd, h⟩
    refine ⟨u, hu, v, hv, d, hd, ?_⟩
    rw [projection_sub_eq, ← add_sub_assoc] at h
    rw [projection_sub_eq, projection_add_eq, projection_add_eq]
    exact sub_eq_zero.mpr (eq_sub_iff_add_eq.mp h)

theorem Conflict.symm {data : Data F n} {i j : Fin n} {b b' : Point F}
    (h : Conflict data i j b b') : Conflict data j i b' b := by
  rcases h with ⟨u, hu, v, hv, d, hd, heq⟩
  refine ⟨v, hv, u, hu, d, ?_, ?_⟩
  · simpa only [Finset.union_comm] using hd
  · rw [projection_sub_eq] at heq ⊢
    exact sub_eq_zero.mpr (sub_eq_zero.mp heq).symm

theorem conflict_comm (data : Data F n) (i j : Fin n) (b b' : Point F) :
    Conflict data i j b b' ↔ Conflict data j i b' b :=
  ⟨Conflict.symm, Conflict.symm⟩

def HasCompatibleChoice (data : Data F n) (pool : Pool F n K) : Prop :=
  ∃ choice : Fin n → Fin K, ∀ i j, i ≠ j →
    ¬ Conflict data i j (pool (i, choice i)) (pool (j, choice j))

def Feasible (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) (b : Point F) : Prop :=
  ∀ e ∈ T, ¬ Conflict data i e.1 b (pool e)

@[simp] theorem feasible_empty (data : Data F n) (pool : Pool F n K)
    (i : Fin n) (b : Point F) : Feasible data ∅ pool i b := by
  simp [Feasible]

theorem feasible_mono (data : Data F n) {S T : Finset (Position n K)}
    (hST : S ⊆ T) (pool : Pool F n K) (i : Fin n) (b : Point F)
    (h : Feasible data T pool i b) : Feasible data S pool i b :=
  fun e he => h e (hST he)

theorem feasible_congr (data : Data F n) (T : Finset (Position n K))
    (pool pool' : Pool F n K) (h : ∀ e ∈ T, pool e = pool' e)
    (i : Fin n) (b : Point F) :
    Feasible data T pool i b ↔ Feasible data T pool' i b := by
  unfold Feasible
  constructor <;> intro hb e he
  · simpa only [h e he] using hb e he
  · simpa only [h e he] using hb e he

section Finite
variable [Fintype F]

def Bounded (D : ℕ) (data : Data F n) : Prop :=
  n ≤ D * Fintype.card F ∧
    (∀ i, (data.W i).card ≤ D) ∧
    (∀ i, (data.dirs i).card ≤ D) ∧
    ∀ d, (Finset.univ.filter fun i => d ∈ data.dirs i).card ≤ D

noncomputable def feasibleSet (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) : Finset (Point F) := by
  classical
  exact Finset.univ.filter (Feasible data T pool i)

@[simp] theorem mem_feasibleSet (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) (b : Point F) :
    b ∈ feasibleSet data T pool i ↔ Feasible data T pool i b := by
  classical
  simp only [feasibleSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem feasibleSet_empty (data : Data F n) (pool : Pool F n K)
    (i : Fin n) : feasibleSet data ∅ pool i = Finset.univ := by
  classical
  ext b
  simp

theorem feasibleSet_mono (data : Data F n) {S T : Finset (Position n K)}
    (hST : S ⊆ T) (pool : Pool F n K) (i : Fin n) :
    feasibleSet data T pool i ⊆ feasibleSet data S pool i := by
  intro b hb
  exact (mem_feasibleSet _ _ _ _ _).mpr
    (feasible_mono data hST pool i b ((mem_feasibleSet _ _ _ _ _).mp hb))

noncomputable def feasibleMass (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) : ℕ :=
  ∑ i ∈ I, (feasibleSet data T pool i).card

def exposedCount (T : Finset (Position n K)) (i : Fin n) : ℕ :=
  (T.filter fun e => e.1 = i).card

end Finite
end RyserCoveringCounterexample.Selection

end OAI
