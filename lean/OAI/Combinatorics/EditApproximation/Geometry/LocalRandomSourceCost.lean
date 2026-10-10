import OAI.Combinatorics.EditApproximation.Geometry.LocalSourceReadCost

namespace OAI

/-! Source charges survive the two adaptive data-gathering stages unchanged.
All table reads have weight zero here; their dependency cost is accounted for
by the projected table program. No accuracy event is used. -/

namespace EditApproximation

section Cost

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (hmass : ∀ input, (readMass input).cost oracle weight = 0)
  (hinitial : ∀ input, (readInitial input).cost oracle weight = 0)
  (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → weight key = 0)
  (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → weight key = 0)
  (groupBound onlineBound : ℕ)
  (hgroup : ∀ key, (readGroup key).cost oracle weight ≤ groupBound)
  (honline : ∀ key range, (readInteger key range).cost oracle weight ≤ onlineBound)

include hmass hinitial hearlier hcurrent hgroup honline

 theorem localRandomBandDataQuery_source_cost_le
    (parentInitial : TargetInterval target.length → ℚ) :
    (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
      (groupScalarKeys M F Q (localGroupQueryKeys N F exponent a parentInitial q)).length * groupBound +
      (localOnlineSourceKeys N P F a parentInitial q).length * onlineBound := by
  unfold localRandomBandDataQuery
  rw [FiniteQuery.cost_collect, FiniteQuery.cost_collect]
  simp only [hmass, hinitial, List.map_const', List.sum_replicate, smul_eq_mul,
    Nat.mul_zero, Nat.zero_add]
  exact localRandomSourceStepQuery_source_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t parentInitial _ _ q readGroup readInteger readEarlier readCurrent
    oracle weight hearlier hcurrent groupBound onlineBound hgroup honline

 theorem localRandomDataQuery_source_cost_le
    (readParent : TargetInterval target.length → FiniteQuery ι)
    (hparent : ∀ r, (readParent r).cost oracle weight = 0) :
    let actualInitial := fun r => (readParent r).value oracle
    (localRandomDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
      (groupScalarKeys M F Q (localGroupQueryKeys N F exponent a actualInitial q)).length * groupBound +
      (localOnlineSourceKeys N P F a actualInitial q).length * onlineBound := by
  dsimp only
  unfold localRandomDataQuery
  rw [FiniteQuery.cost_bind, hparent q, Nat.zero_add, FiniteQuery.cost_collect]
  simp only [hparent, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_zero, Nat.zero_add]
  let keys := refinementInitialSupport N P F exponent a ((readParent q).value oracle) q
  let cached := finiteAnswerTable keys (keys.map fun r => (readParent r).value oracle)
  have hq : cached q = (readParent q).value oracle :=
    finiteAnswerTable_map keys _ q (refinementInitialSupport_query N P F exponent a _ q)
  have hb := localRandomBandDataQuery_source_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t readMass readInitial readGroup readInteger q readEarlier readCurrent
    oracle weight hmass hinitial hearlier hcurrent groupBound onlineBound hgroup honline cached
  change (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
    cached readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤ _
  apply hb.trans
  simp only [localGroupQueryKeys, localOnlineSourceKeys, hq]
  exact le_rfl

end Cost

end EditApproximation

end OAI
