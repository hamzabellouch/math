import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomTableCost
import OAI.Combinatorics.EditApproximation.Refinement.ComputedRefinementReadBudget

namespace OAI

/-! The source-aware query satisfies the same table branching budgets.
Its group/online values may be arbitrary: only source-free table costs
and nonnegativity of the actual initial value are needed here. -/

namespace EditApproximation

 theorem computed_localRandomDataQuery_table_cost {ι α : Type*} (source target : List α)
    {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P H T t : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
    (ht : 0 < t) (htime : t ≤ (integerParameters N).S)
    (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (readParent : TargetInterval target.length → FiniteQuery ι)
    (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
    (readGroup : GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery ι)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (q : TargetInterval target.length)
    (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (oracle : ι → ℚ) (weight : ι → ℕ) (dataCost earlierCost currentCost : ℕ)
    (hparent : ∀ r, (readParent r).cost oracle weight ≤ dataCost)
    (hmass : ∀ key, (readMass key).cost oracle weight ≤ T * dataCost)
    (hinitial : ∀ key, (readInitial key).cost oracle weight ≤ dataCost)
    (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
    (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
    (hearlier : ∀ key, (readEarlier key).cost oracle weight ≤ earlierCost)
    (hcurrent : ∀ key, (readCurrent key).cost oracle weight ≤ currentCost)
    (hw : 0 ≤ (readParent q).value oracle) :
    let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
    (localRandomDataQuery source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
        (2 + 2 * B) * dataCost + B * earlierCost +
          (2 * M * inputSmallLog N ^ 256) * currentCost := by
  dsimp only
  let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
  let actual := fun r => (readParent r).value oracle
  have hdata := computed_data_support_budget parent N P T hN hell hM hP hT A hA actual q hw
  have hband (parentInitial : TargetInterval target.length → ℚ) (hq : parentInitial q = actual q) :
      (refinementBandInputList (M := M) parent N P (inputSmallLog N) (40 * smallLogExponent N)
        (refinementFactor A (inputSmallLog N)) parentInitial q).length *
        (T * dataCost + dataCost) ≤ B * dataCost := by
    have hb := (computed_data_support_budget parent N P T hN hell hM hP hT A hA
      parentInitial q (by rw [hq]; exact hw)).2
    convert Nat.mul_le_mul_right dataCost hb using 1
    ring
  have hstep (parentInitial : TargetInterval target.length → ℚ) (hq : parentInitial q = actual q)
      (child initial : Fin M → TargetInterval target.length → ℚ)
      (draw : CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
      (integer : ℕ → TargetInterval target.length → ℕ) :
      (localRefinementStepQuery source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta t
        parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤
          B * earlierCost + (2 * M * inputSmallLog N ^ 256) * currentCost := by
    let earlier := fun i s r => (readEarlier (i, s, r)).value oracle
    let current := fun i r => (readCurrent (i, r)).value oracle
    have he := computed_queryEarlierHistory_card parent N P t hN hell hP (by omega) A hA
      parentInitial q (by rw [hq]; exact hw)
    rw [← hM] at he
    have hc : (currentQueryInputCover source target parent N P (inputSmallLog N)
        (40 * smallLogExponent N) (inputSmallLog N ^ 80) tau
        (refinementFactor A (inputSmallLog N)) parentInitial child initial current draw q
        (localOnlineCandidates source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
          H tau (refinementFactor A (inputSmallLog N)) eta kappa parentInitial child initial earlier
          (t - 1) integer q)).card ≤ M * inputSmallLog N ^ 256 := by
      subst M
      exact computed_currentQueryInputCover_card source target N P hN hell parent A tau hA
        parentInitial child initial current draw q (by rw [hq]; exact hw) _
        (localOnlineCandidates_length source target parent N P (inputSmallLog N)
          (40 * smallLogExponent N) H tau (refinementFactor A (inputSmallLog N)) eta kappa
          parentInitial child initial earlier (t - 1) integer q)
    have hs := localRefinementStepQuery_cost_le source target parent N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
      (refinementFactor A (inputSmallLog N)) eta kappa delta t parentInitial child initial draw integer q
      readEarlier readCurrent oracle weight earlier current ht (fun _ => rfl) (fun _ => rfl)
      earlierCost currentCost hearlier hcurrent
    apply hs.trans
    apply Nat.add_le_add (Nat.mul_le_mul_right earlierCost he)
    convert Nat.mul_le_mul_right currentCost (Nat.mul_le_mul_left 2 hc) using 1
    ring
  have h := localRandomDataQuery_table_cost_le source target parent N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
    (refinementFactor A (inputSmallLog N)) eta kappa delta t readParent readMass readInitial
    readGroup readInteger q readEarlier readCurrent oracle weight dataCost (T * dataCost) dataCost
    (B * dataCost) (B * earlierCost + (2 * M * inputSmallLog N ^ 256) * currentCost)
    hparent hmass hinitial hgroup honline hband hstep
  have hi := Nat.mul_le_mul_right dataCost (Nat.add_le_add_left hdata.1 1)
  dsimp only [B, actual] at h hi ⊢
  nlinarith only [h, hi]

end EditApproximation

end OAI
