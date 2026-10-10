import Mathlib
import OAI.Computability.VertexCover.Analysis.BaseReductionCoherent

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open UniqueGames.Foundations.Games
noncomputable section

def occurrenceLaw (Φ : LabelCover) : FiniteDistribution (Fin Φ.M) := by
  letI : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  exact FiniteDistribution.uniform (Fin Φ.M)

def questionProjection (Φ : LabelCover) (x : Fin Φ.u) (y : Fin Φ.v) (a : Fin Φ.qU) : Fin Φ.qV :=
  if h : ∃ e, Φ.left e = x ∧ Φ.right e = y then Φ.projection h.choose a
  else ⟨0, Φ.qV_pos⟩

theorem questionProjection_at (Φ : LabelCover) (hc : Φ.ParallelCoherent)
    (e : Fin Φ.M) (a : Fin Φ.qU) :
    Φ.questionProjection (Φ.left e) (Φ.right e) a = Φ.projection e a := by
  unfold questionProjection
  split
  · rename_i h
    exact congrFun (hc h.choose e h.choose_spec.1 h.choose_spec.2) a
  · rename_i h
    exact False.elim (h ⟨e, rfl, rfl⟩)

def asGame (Φ : LabelCover) : Game (Fin Φ.u) (Fin Φ.v) (Fin Φ.qU) (Fin Φ.qV) :=
  { questions := Φ.occurrenceLaw.pushforward (fun e => (Φ.left e, Φ.right e))
    accepts := fun x y a b => decide (Φ.questionProjection x y a = b) }

theorem asGame_success (Φ : LabelCover) (hc : Φ.ParallelCoherent) (A : Φ.Labeling) :
    Φ.asGame.success A = (Φ.satisfiedCount A : ℝ) / Φ.M := by
  classical
  change (Φ.occurrenceLaw.pushforward (fun e => (Φ.left e, Φ.right e))).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  simp only [FiniteDistribution.probability, Game.wins, asGame, questionProjection_at Φ hc,
    decide_eq_true_eq]
  simp only [occurrenceLaw, FiniteDistribution.uniform, Fintype.card_fin]
  change (∑ e, if Φ.Satisfies A e then 1 / (Φ.M : ℝ) else 0) = _
  calc
    _ = (∑ e, (if Φ.Satisfies A e then 1 else 0 : ℝ)) / Φ.M := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    _ = _ := by rw [Finset.sum_boole]; rfl

def asGameValue (Φ : LabelCover) : ℝ := by
  letI : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩
  letI : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩
  exact Φ.asGame.value

theorem asGameValue_eq (Φ : LabelCover) (hc : Φ.ParallelCoherent) : Φ.asGameValue = Φ.value := by
  classical
  let : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩
  let : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩
  change Φ.asGame.value = Φ.value
  apply le_antisymm
  · apply (Φ.asGame.value_le_iff _).mpr
    intro A
    rw [asGame_success Φ hc A]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Φ.satisfiedCount_le_max A)) (by positivity)
  · apply value_le_of_counts
    intro A
    have hs := Φ.asGame.success_le_value A
    rw [asGame_success Φ hc A] at hs
    exact (div_le_iff₀ (Nat.cast_pos.mpr Φ.M_pos)).mp hs

def tupleEquiv (a n : ℕ) : (Fin n → Fin a) ≃ Fin (a ^ n) :=
  Fintype.equivFinOfCardEq (by simp)

def parallelPower (Φ : LabelCover) (n : ℕ) : LabelCover where
  u := Φ.u ^ n
  v := Φ.v ^ n
  qU := Φ.qU ^ n
  qV := Φ.qV ^ n
  M := Φ.M ^ n
  qU_pos := pow_pos Φ.qU_pos _
  qV_pos := pow_pos Φ.qV_pos _
  M_pos := pow_pos Φ.M_pos _
  left e := tupleEquiv Φ.u n (fun i => Φ.left ((tupleEquiv Φ.M n).symm e i))
  right e := tupleEquiv Φ.v n (fun i => Φ.right ((tupleEquiv Φ.M n).symm e i))
  projection e a := tupleEquiv Φ.qV n (fun i => Φ.projection ((tupleEquiv Φ.M n).symm e i)
    ((tupleEquiv Φ.qU n).symm a i))

def repeatLabeling (Φ : LabelCover) (n : ℕ) (A : Φ.Labeling) : (Φ.parallelPower n).Labeling :=
  (fun x => tupleEquiv Φ.qU n (fun i => A.1 ((tupleEquiv Φ.u n).symm x i)),
   fun y => tupleEquiv Φ.qV n (fun i => A.2 ((tupleEquiv Φ.v n).symm y i)))

theorem repeat_perfect (Φ : LabelCover) (n : ℕ) (A : Φ.Labeling) (hA : ∀ e, Φ.Satisfies A e) :
    ∀ e, (Φ.parallelPower n).Satisfies (Φ.repeatLabeling n A) e := by
  intro e
  change tupleEquiv Φ.qV n _ = tupleEquiv Φ.qV n _
  apply congrArg (tupleEquiv Φ.qV n)
  funext i
  simpa only [Satisfies, repeatLabeling, parallelPower, Equiv.symm_apply_apply] using hA ((tupleEquiv Φ.M n).symm e i)

def repeatedStrategy (Φ : LabelCover) (n : ℕ) (A : (Φ.parallelPower n).Labeling) :
    Strategy (Fin n → Fin Φ.u) (Fin n → Fin Φ.v) (Fin n → Fin Φ.qU) (Fin n → Fin Φ.qV) :=
  (fun x => (tupleEquiv Φ.qU n).symm (A.1 (tupleEquiv Φ.u n x)),
   fun y => (tupleEquiv Φ.qV n).symm (A.2 (tupleEquiv Φ.v n y)))

theorem repetition_success_probability (Φ : LabelCover) (hc : Φ.ParallelCoherent) (n : ℕ)
    (B : Strategy (Fin n → Fin Φ.u) (Fin n → Fin Φ.v)
      (Fin n → Fin Φ.qU) (Fin n → Fin Φ.qV)) :
    (Φ.asGame.repetition n).success B = (Φ.occurrenceLaw.iid n).probability
      (fun es => decide (∀ i, Φ.projection (es i)
        (B.1 (fun j => Φ.left (es j)) i) = B.2 (fun j => Φ.right (es j)) i)) := by
  classical
  unfold Game.success
  change (((Φ.occurrenceLaw.pushforward (fun e => (Φ.left e, Φ.right e))).iid n).transport
    (Game.tupleQuestionEquiv n)).probability _ = _
  rw [FiniteDistribution.probability_transport, FiniteDistribution.iid_pushforward,
    FiniteDistribution.probability_pushforward]
  congr 1
  funext es
  simp only [Game.wins, Game.repetition, Game.tupleQuestionEquiv, asGame,
    Equiv.coe_fn_mk, questionProjection_at Φ hc, decide_eq_true_eq]

theorem power_satisfies_iff (Φ : LabelCover) (n : ℕ) (A : (Φ.parallelPower n).Labeling)
    (es : Fin n → Fin Φ.M) :
    (Φ.parallelPower n).Satisfies A (tupleEquiv Φ.M n es) ↔
      ∀ i, Φ.projection (es i)
        ((Φ.repeatedStrategy n A).1 (fun j => Φ.left (es j)) i) =
        (Φ.repeatedStrategy n A).2 (fun j => Φ.right (es j)) i := by
  simp only [Satisfies, parallelPower, repeatedStrategy, Equiv.symm_apply_apply]
  rw [← Equiv.eq_symm_apply]
  exact funext_iff

theorem repetition_success (Φ : LabelCover) (hc : Φ.ParallelCoherent) (n : ℕ)
    (A : (Φ.parallelPower n).Labeling) :
    (Φ.asGame.repetition n).success (Φ.repeatedStrategy n A) =
      ((Φ.parallelPower n).satisfiedCount A : ℝ) / (Φ.M ^ n : ℕ) := by
  classical
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  rw [repetition_success_probability Φ hc]
  have hlaw : Φ.occurrenceLaw.iid n = FiniteDistribution.uniform (Fin n → Fin Φ.M) :=
    FiniteDistribution.iid_uniform n
  rw [hlaw]
  simp only [← power_satisfies_iff Φ n A, FiniteDistribution.probability,
    FiniteDistribution.uniform, Fintype.card_fun, Fintype.card_fin, decide_eq_true_eq]
  calc
    _ = ∑ e : Fin (Φ.M ^ n), if (Φ.parallelPower n).Satisfies A e then
        1 / ((Φ.M ^ n : ℕ) : ℝ) else 0 :=
      Fintype.sum_equiv (tupleEquiv Φ.M n) _ _ (fun _ => rfl)
    _ = (∑ e : Fin (Φ.M ^ n), (if (Φ.parallelPower n).Satisfies A e then 1 else 0 : ℝ)) /
        (Φ.M ^ n : ℕ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    _ = _ := by
      have hsum : (∑ e : Fin (Φ.parallelPower n).M,
          (@ite ℝ ((Φ.parallelPower n).Satisfies A e) (Classical.propDecidable _) 1 0)) =
          ((Φ.parallelPower n).satisfiedCount A : ℝ) := by
        rw [satisfiedCount, Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : (Φ.parallelPower n).Satisfies A e <;> simp only [h, ite_true, ite_false, Nat.cast_zero, Nat.cast_one]
      exact congrArg (fun x : ℝ => x / ((Φ.M ^ n : ℕ) : ℝ)) hsum

theorem power_value_le_repetition (Φ : LabelCover) (hc : Φ.ParallelCoherent) (n : ℕ) :
    (Φ.parallelPower n).value ≤
      (letI : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩;
       letI : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩;
       (Φ.asGame.repetition n).value) := by
  classical
  let : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩
  let : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩
  apply value_le_of_counts
  intro A
  have hs := (Φ.asGame.repetition n).success_le_value (Φ.repeatedStrategy n A)
  rw [repetition_success Φ hc] at hs
  exact (div_le_iff₀ (Nat.cast_pos.mpr (pow_pos Φ.M_pos n))).mp hs

end
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
