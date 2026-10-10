import OAI.Combinatorics.Ryser.Selection.Definitions
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import OAI.Combinatorics.Ryser.Probability.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

theorem uniform_prob_projection (d : Direction F) (c : F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => projection d b = c) =
      1 / (Fintype.card F : ℝ) := by
  classical
  rw [FiniteLaw.uniform_prob]
  calc
    _ = ((linePoints (d, c)).card : ℝ) / (Fintype.card (Point F) : ℝ) := by
      apply congrArg (fun T : Finset (Point F) =>
        (T.card : ℝ) / (Fintype.card (Point F) : ℝ))
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_linePoints, Incidence]
    _ = _ := by
      rw [card_linePoints, card_point, Nat.cast_pow]
      have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

abbrev EquationIndex (data : Data F n) (i j : Fin n) :=
  ↥(data.W i) × ↥(data.W j) × ↥(data.dirs i ∪ data.dirs j)

def equationEvent (data : Data F n) (i j : Fin n) (b' : Point F)
    (e : EquationIndex data i j) (b : Point F) : Prop :=
  projection e.2.2.val b = projection e.2.2.val b' +
    projection e.2.2.val (e.2.1.val - e.1.val)

theorem conflict_iff_equation (data : Data F n) (i j : Fin n) (b b' : Point F) :
    Conflict data i j b b' ↔ ∃ e : EquationIndex data i j, equationEvent data i j b' e b := let _ := instFintypeF; by
  rw [conflict_iff_forbidden]
  constructor
  · rintro ⟨u, hu, v, hv, d, hd, h⟩
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩, ⟨d, hd⟩), h⟩
  · rintro ⟨⟨u, v, d⟩, h⟩
    exact ⟨u.val, u.property, v.val, v.property, d.val, d.property, h⟩

theorem card_equationIndex_le {D : ℕ} (data : Data F n) (hdata : Bounded D data)
    (i j : Fin n) : Fintype.card (EquationIndex data i j) ≤ 2 * D ^ 3 := by
  have hdirs : (data.dirs i ∪ data.dirs j).card ≤ D + D :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (hdata.2.2.1 i) (hdata.2.2.1 j))
  calc
    Fintype.card (EquationIndex data i j) =
        (data.W i).card * ((data.W j).card * (data.dirs i ∪ data.dirs j).card) := by
      simp only [EquationIndex, Fintype.card_prod, Fintype.card_coe]
    _ ≤ D * (D * (D + D)) :=
      Nat.mul_le_mul (hdata.2.1 i) (Nat.mul_le_mul (hdata.2.1 j) hdirs)
    _ = 2 * D ^ 3 := by ring

theorem prob_conflict_le {D : ℕ} (data : Data F n) (hdata : Bounded D data)
    (i j : Fin n) (b' : Point F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => Conflict data i j b b') ≤
      (2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ) := by
  classical
  have hP : (fun b => Conflict data i j b b') =
      (fun b => ∃ e : EquationIndex data i j, equationEvent data i j b' e b) := by
    funext b
    exact propext (conflict_iff_equation data i j b b')
  rw [hP]
  calc
    _ ≤ ∑ e : EquationIndex data i j,
        (FiniteLaw.uniform (Point F)).prob (equationEvent data i j b' e) :=
      FiniteLaw.prob_exists_le _ _
    _ = (Fintype.card (EquationIndex data i j) : ℝ) / (Fintype.card F : ℝ) := by
      calc
        _ = ∑ _e : EquationIndex data i j, 1 / (Fintype.card F : ℝ) := by
          apply Finset.sum_congr rfl
          intro e _
          exact uniform_prob_projection e.2.2.val
            (projection e.2.2.val b' + projection e.2.2.val (e.2.1.val - e.1.val))
        _ = _ := by simp [div_eq_mul_inv]
    _ ≤ (2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast card_equationIndex_le data hdata i j

theorem prob_not_feasible_le {D : ℕ} (data : Data F n) (hdata : Bounded D data)
    (T : Finset (Position n K)) (pool : Pool F n K) (i : Fin n) :
    (FiniteLaw.uniform (Point F)).prob (fun b => ¬Feasible data T pool i b) ≤
      (T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) := by
  classical
  have hP : (fun b => ¬Feasible data T pool i b) =
      (fun b => ∃ e : ↥T, Conflict data i e.val.1 b (pool e.val)) := by
    funext b
    simp [Feasible]
  rw [hP]
  calc
    _ ≤ ∑ e : ↥T, (FiniteLaw.uniform (Point F)).prob
        (fun b => Conflict data i e.val.1 b (pool e.val)) :=
      FiniteLaw.prob_exists_le _ _
    _ ≤ ∑ _e : ↥T, ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) :=
      Finset.sum_le_sum (fun e _ => prob_conflict_le data hdata i e.val.1 (pool e.val))
    _ = _ := by simp

end RyserCoveringCounterexample.Selection

end OAI
