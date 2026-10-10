import OAI.Combinatorics.Ryser.Selection.PoolLaw
import OAI.Combinatorics.Ryser.Geometry.Cardinality

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

noncomputable def feasibleDensity (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) : ℝ :=
  (FiniteLaw.uniform (Point F)).prob (Feasible data T pool i)

theorem feasibleDensity_nonneg (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) : 0 ≤ feasibleDensity data T pool i :=
  (FiniteLaw.uniform (Point F)).prob_nonneg _

theorem feasibleDensity_le_one (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) : feasibleDensity data T pool i ≤ 1 :=
  (FiniteLaw.uniform (Point F)).prob_le_one _

theorem feasibleDensity_eq_card (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) :
    feasibleDensity data T pool i =
      ((feasibleSet data T pool i).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  rw [feasibleDensity, FiniteLaw.uniform_prob, card_point, Nat.cast_pow]
  rfl

theorem prob_not_feasible_eq (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) :
    (FiniteLaw.uniform (Point F)).prob (fun b => ¬Feasible data T pool i b) =
      1 - feasibleDensity data T pool i :=
  (FiniteLaw.uniform (Point F)).prob_compl _

theorem sum_feasibleDensity (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) :
    (∑ i ∈ I, feasibleDensity data T pool i) =
      (feasibleMass data I T pool : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  simp only [feasibleDensity_eq_card, feasibleMass, Nat.cast_sum,
    div_eq_mul_inv, Finset.sum_mul]

theorem feasibleSet_join_eq (data : Data F n) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T)
    (i : Fin n) :
    feasibleSet data T (joinAssignments T x y) i =
      feasibleSet data T (frozenPool T x) i := by
  ext b
  simp only [mem_feasibleSet, feasible_join_iff]

theorem feasibleMass_join_eq (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (x : ExposedAssignment (F := F) T)
    (y : FreshAssignment (F := F) T) :
    feasibleMass data I T (joinAssignments T x y) =
      feasibleMass data I T (frozenPool T x) := by
  simp only [feasibleMass, feasibleSet_join_eq]

theorem prob_feasibleMass_lt_eq_exposed (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (a : ℝ) :
    (poolLaw F n K).prob (fun pool => (feasibleMass data I T pool : ℝ) < a) =
      (FiniteLaw.uniform (ExposedAssignment (F := F) T)).prob
        (fun x => (feasibleMass data I T (frozenPool T x) : ℝ) < a) := by
  classical
  rw [poolLaw_prob_split T]
  simp only [feasibleMass_join_eq]
  have hc (x : ExposedAssignment (F := F) T) :
      (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
          (fun _ => (feasibleMass data I T (frozenPool T x) : ℝ) < a) =
        if (feasibleMass data I T (frozenPool T x) : ℝ) < a then 1 else 0 := by
    split_ifs with hx <;> simp [hx]
  simp_rw [hc]
  exact ((FiniteLaw.uniform (ExposedAssignment (F := F) T)).prob_eq_expectation _).symm

end RyserCoveringCounterexample.Selection

end OAI
