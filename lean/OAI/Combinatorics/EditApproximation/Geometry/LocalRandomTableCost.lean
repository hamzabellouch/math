import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomSourceCost

namespace OAI

/-! Random source reads have zero table charge. Uniform bounds for the
remaining local step therefore lift through the actual source collectors,
including the adaptive data queries. -/

namespace EditApproximation

section Step

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ) (stepBudget : ℕ)
  (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
  (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
  (hstep : ∀ draw integer,
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤ stepBudget)

include hgroup honline hstep in
 theorem localRandomSourceStepQuery_table_cost_le :
    (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).cost oracle weight ≤ stepBudget := by
  unfold localRandomSourceStepQuery
  rw [FiniteQuery.cost_collect]
  simp only [hgroup, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_zero, Nat.zero_add]
  rw [localOnlineSourceStepQuery_cost]
  dsimp only
  simp only [honline, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_zero, Nat.zero_add]
  exact hstep _ _

end Step

section Band

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (massBudget initialBudget stepBudget : ℕ)
  (hmass : ∀ key, (readMass key).cost oracle weight ≤ massBudget)
  (hinitial : ∀ key, (readInitial key).cost oracle weight ≤ initialBudget)
  (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
  (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
  (hstep : ∀ child initial draw integer,
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤ stepBudget)

include hmass hinitial hgroup honline hstep in
 theorem localRandomBandDataQuery_table_cost_le :
    (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
    (refinementBandInputList (M := M) parent N P F exponent a parentInitial q).length *
      (massBudget + initialBudget) + stepBudget := by
  let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  let mass := fun i r => finiteAnswerTable keys (keys.map fun input => (readMass input).value oracle) (i, r)
  let initial' := fun i r => finiteAnswerTable keys (keys.map fun input => (readInitial input).value oracle) (i, r)
  have hm := list_map_sum_le_constant keys (fun input => (readMass input).cost oracle weight) massBudget hmass
  have hi := list_map_sum_le_constant keys (fun input => (readInitial input).cost oracle weight) initialBudget hinitial
  have hs := localRandomSourceStepQuery_table_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t parentInitial mass initial' readGroup readInteger q readEarlier readCurrent
    oracle weight stepBudget hgroup honline (hstep mass initial')
  unfold localRandomBandDataQuery
  rw [FiniteQuery.cost_collect, FiniteQuery.cost_collect]
  change _ + (_ + (localRandomSourceStepQuery source target parent N P F exponent H Q
    tau a eta kappa delta t parentInitial mass initial' q readGroup readInteger readEarlier readCurrent).cost
      oracle weight) ≤ keys.length * (massBudget + initialBudget) + stepBudget
  nlinarith only [hm, hi, hs]

end Band

section Data

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readParent : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (parentBudget massBudget initialBudget bandBudget stepBudget : ℕ)
  (hparent : ∀ r, (readParent r).cost oracle weight ≤ parentBudget)
  (hmass : ∀ key, (readMass key).cost oracle weight ≤ massBudget)
  (hinitial : ∀ key, (readInitial key).cost oracle weight ≤ initialBudget)
  (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
  (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
  (hband : ∀ parentInitial : TargetInterval target.length → ℚ,
    parentInitial q = (readParent q).value oracle →
    (refinementBandInputList (M := M) parent N P F exponent a parentInitial q).length *
      (massBudget + initialBudget) ≤ bandBudget)
  (hstep : ∀ parentInitial : TargetInterval target.length → ℚ,
    parentInitial q = (readParent q).value oracle → ∀ child initial draw integer,
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤ stepBudget)

include hparent hmass hinitial hgroup honline hband hstep in
 theorem localRandomDataQuery_table_cost_le :
    (localRandomDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
      (1 + (refinementInitialSupport N P F exponent a ((readParent q).value oracle) q).length) *
        parentBudget + bandBudget + stepBudget := by
  let keys := refinementInitialSupport N P F exponent a ((readParent q).value oracle) q
  let cached := finiteAnswerTable keys (keys.map fun r => (readParent r).value oracle)
  have hq : cached q = (readParent q).value oracle :=
    finiteAnswerTable_map keys _ q (refinementInitialSupport_query N P F exponent a _ q)
  have hlast := localRandomBandDataQuery_table_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t cached readMass readInitial readGroup readInteger q readEarlier readCurrent
    oracle weight massBudget initialBudget stepBudget hmass hinitial hgroup honline (hstep cached hq)
  have hlast' := hlast.trans (Nat.add_le_add_right (hband cached hq) stepBudget)
  have hfirst := hparent q
  have hsum := list_map_sum_le_constant keys (fun r => (readParent r).cost oracle weight) parentBudget hparent
  unfold localRandomDataQuery
  rw [FiniteQuery.cost_bind, FiniteQuery.cost_collect]
  change _ + (_ + (localRandomBandDataQuery source target parent N P F exponent H Q
    tau a eta kappa delta t cached readMass readInitial readGroup readInteger q readEarlier readCurrent).cost
      oracle weight) ≤ _
  change _ ≤ (1 + keys.length) * parentBudget + bandBudget + stepBudget
  nlinarith only [hfirst, hsum, hlast']

end Data

end EditApproximation

end OAI
