import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedKeys
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomCoarseOracle
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomMemo

namespace OAI

namespace EditApproximation

section Keys

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ) (initial : PhysicalEntry M J target.length → ℕ)

local notation "mixed" => chargedRandomGlobalQuery source target N P F exponent H Q T S
  passes copies factor multiplier tau eta kappa delta readGroup readInteger initial
local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank mixed sourceAnswer
local notation "coarse" => chargedRandomCoarseQuery source target N P F exponent H Q T S
  passes copies factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer

 theorem chargedRandomCoarseQuery_uncached_keys
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (entry : PhysicalEntry M J target.length)
    (hentry : Sum.inl entry ∈ rankedUncachedKeys ChargedPhysicalRequest.rank program root) :
    entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
  have hall : ∀ level root, root.rank = level → ∀ entry,
      Sum.inl entry ∈ rankedUncachedKeys ChargedPhysicalRequest.rank program root →
      entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel entry he
      cases root with
      | inl base =>
        rw [rankedUncachedKeys] at he
        simp only [SourceRanked.projectedBody, chargedRandomGlobalQuery,
          FiniteQuery.eraseSources, FiniteQuery.keys, List.flatMap_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inl.injEq] at he
        subst entry
        rw [chargedRandomCoarseQuery]
        exact List.mem_cons_self
      | inr parent =>
        rw [rankedUncachedKeys] at he
        rcases List.mem_cons.mp he with he | he
        · cases he
        obtain ⟨child, hc, he⟩ := List.mem_flatMap.mp he
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_keys]
        apply List.mem_flatMap.mpr
        refine ⟨child, ?_, ih child.val.rank (hlevel ▸ child.property) child.val rfl entry he⟩
        have hv (child) := chargedRandomCoarseQuery_value source target N P F exponent H Q T S
          passes copies factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial child
        simp_rw [hv]
        unfold SourceRanked.projectedBody
        rw [chargedRandomGlobalQuery_table_initial_independent source target N P F exponent H Q T S
          passes copies factor multiplier tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        exact hc
  exact hall root.rank root rfl entry hentry

 theorem chargedRandomMemo_coarse_key
    (values : ChargedPhysicalRequest M J target.length passes copies T S → ℚ)
    (hbody : ∀ key, (mixed key).value (Sum.elim sourceAnswer (fun next => values next.val)) = values key)
    (bits : ℕ) (encode : Sum σ (ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (entry : PhysicalEntry M J target.length)
    (hentry : Sum.inr (Sum.inl entry) ∈
      (chargedRandomMemoEvaluate source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger initial sourceAnswer bits encode root).freshKeys) :
    entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
  apply chargedRandomCoarseQuery_uncached_keys source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial root entry
  apply SourceRanked.uncachedKeys_table_mem ChargedPhysicalRequest.rank mixed sourceAnswer values hbody root
    (Sum.inl entry)
  exact rankedMemoEvaluate_freshKeys_mem _ _ bits encode hinjective hbounded (.inr root) .empty
    (memoSound_empty _ _ _) (.inr (.inl entry)) hentry

end Keys

end EditApproximation

end OAI
