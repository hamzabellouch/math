import OAI.Analysis.Nonexpansive.WeightedTree
import OAI.Analysis.Nonexpansive.PredictionCompact
import OAI.Analysis.Nonexpansive.FinitePrefixEmbedding

namespace OAI

/-!
# All candidates and the retained ordered level

The candidate ledger keeps discarded labels. An order embedding selects the
actual children. Their coefficients extend by zero to discarded candidates;
restricting these coefficients to the earlier candidate prefix gives the
actual prediction parameter and the exact ideal child-average identity.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- A completed candidate level, including every discarded candidate. -/
structure CandidateLedger (T : OrderedTree) (k : ℕ) (Y : Type*) where
  count : ℕ
  parent : Fin count → T.Node k
  parent_monotone : Monotone parent
  point : Fin count → Y
  retain : T.Node (k + 1) ↪o Fin count
  parent_retain : ∀ v, parent (retain v) = T.parent k v

namespace CandidateLedger

variable {T : OrderedTree} {k : ℕ} {Y : Type*}
variable (L : CandidateLedger T k Y)

def retainedPoint (v : T.Node (k + 1)) : Y := L.point (L.retain v)

/-- Retained weights at retained candidates, and zero at discarded candidates. -/
def coefficient (W : WeightedTree T) : Fin L.count → ℝ :=
  Function.extend L.retain (W.weight k) (fun _ => 0)

@[simp] theorem coefficient_retain (W : WeightedTree T) (v : T.Node (k + 1)) :
    L.coefficient W (L.retain v) = W.weight k v := by
  exact L.retain.injective.extend_apply (W.weight k) (fun _ => 0) v

theorem coefficient_discarded (W : WeightedTree T) (c : Fin L.count)
    (hc : ¬ ∃ v, L.retain v = c) : L.coefficient W c = 0 := by
  exact Function.extend_apply' (W.weight k) (fun _ => 0) c hc

theorem coefficient_nonneg (W : WeightedTree T) (c : Fin L.count) :
    0 ≤ L.coefficient W c := by
  by_cases hc : ∃ v, L.retain v = c
  · obtain ⟨v, rfl⟩ := hc
    rw [L.coefficient_retain]
    exact W.weight_nonneg k v
  · rw [L.coefficient_discarded W c hc]

theorem coefficient_pos_iff (W : WeightedTree T) (c : Fin L.count) :
    0 < L.coefficient W c ↔ ∃ v, L.retain v = c := by
  constructor
  · intro hpos
    by_contra hc
    rw [L.coefficient_discarded W c hc] at hpos
    exact (lt_irrefl 0) hpos
  · rintro ⟨v, rfl⟩
    rw [L.coefficient_retain]
    exact W.weight_pos k v

theorem coefficient_eq_zero_iff (W : WeightedTree T) (c : Fin L.count) :
    L.coefficient W c = 0 ↔ ¬ ∃ v, L.retain v = c := by
  constructor
  · intro hz hc
    have hp := (L.coefficient_pos_iff W c).2 hc
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · exact L.coefficient_discarded W c

/-- Every full candidate parent group has exactly the actual child mass one. -/
theorem coefficientSum_eq_one (W : WeightedTree T) (p : T.Node k) :
    Prediction.coefficientSum L.parent (L.coefficient W) p = 1 := by
  classical
  unfold Prediction.coefficientSum
  calc
    (∑ c, Prediction.groupedCoefficient L.parent (L.coefficient W) p c) =
        ∑ v, Prediction.groupedCoefficient L.parent (L.coefficient W) p
          (L.retain v) := by
      apply FinitePrefix.sum_univ_supported_embedding L.retain.toEmbedding
      intro c hc
      simp [Prediction.groupedCoefficient, L.coefficient_discarded W c hc]
    _ = 1 := by
      simpa only [Prediction.groupedCoefficient, L.parent_retain,
        L.coefficient_retain, Finset.sum_filter] using W.weight_sum k p

theorem coefficient_mem_coefficientSet (W : WeightedTree T) :
    L.coefficient W ∈ Prediction.coefficientSet L.parent := by
  refine ⟨L.coefficient_nonneg W, ?_⟩
  intro p
  exact (L.coefficientSum_eq_one W p).le

/-- Earlier candidates include discarded entries and omit the current entry. -/
abbrev Earlier (v : T.Node (k + 1)) := Fin (L.retain v).val

def earlierInclusion (v : T.Node (k + 1)) : L.Earlier v ↪ Fin L.count :=
  FinitePrefix.inclusion (L.retain v).isLt.le

def earlierParent (v : T.Node (k + 1)) : L.Earlier v → T.Node k :=
  fun c => L.parent (L.earlierInclusion v c)

def earlierPoint (v : T.Node (k + 1)) : L.Earlier v → Y :=
  fun c => L.point (L.earlierInclusion v c)

def actualTheta (W : WeightedTree T) (v : T.Node (k + 1)) : L.Earlier v → ℝ :=
  fun c => L.coefficient W (L.earlierInclusion v c)

/-- The restricted candidate parameter obeys every parent budget. -/
theorem actualTheta_mem (W : WeightedTree T) (v : T.Node (k + 1)) :
    L.actualTheta W v ∈ Prediction.coefficientSet (L.earlierParent v) := by
  refine ⟨fun c => L.coefficient_nonneg W (L.earlierInclusion v c), ?_⟩
  intro p
  calc
    Prediction.coefficientSum (L.earlierParent v) (L.actualTheta W v) p =
        ∑ c : Fin L.count, if c.val < (L.retain v).val then
          Prediction.groupedCoefficient L.parent (L.coefficient W) p c else 0 := by
      exact FinitePrefix.sum_prefix_eq_sum_cutoff (L.retain v).isLt.le
        (Prediction.groupedCoefficient L.parent (L.coefficient W) p)
    _ ≤ Prediction.coefficientSum L.parent (L.coefficient W) p := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs
      · exact le_refl _
      · exact Prediction.groupedCoefficient_nonneg L.parent
          (L.coefficient_nonneg W) p c
    _ = 1 := L.coefficientSum_eq_one W p

/-- The ledger's chronological order restricts to the retained level order. -/
theorem retained_before_iff (v w : T.Node (k + 1)) :
    (L.retain w).val < (L.retain v).val ↔ w < v := by
  change L.retain w < L.retain v ↔ w < v
  exact L.retain.lt_iff_lt

section AffineIdentity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The correction predicted from all earlier candidates equals the correction
from exactly the earlier retained children. Discarded terms vanish by definition. -/
theorem actualTheta_correction (W : WeightedTree T) (v : T.Node (k + 1))
    (val : Y → X) (b : X) (p : T.Node k) :
    (∑ c : L.Earlier v,
      Prediction.groupedCoefficient (L.earlierParent v) (L.actualTheta W v) p c •
        (val (L.earlierPoint v c) - b)) =
      ∑ w ∈ Finset.univ.filter (fun w => T.parent k w = p),
        if w < v then W.weight k w • (val (L.retainedPoint w) - b) else 0 := by
  classical
  calc
    _ = ∑ w : T.Node (k + 1), if w < v then
        Prediction.groupedCoefficient L.parent (L.coefficient W) p (L.retain w) •
          (val (L.point (L.retain w)) - b) else 0 := by
      exact
        (FinitePrefix.sum_prefix_eq_sum_retained (M := X) L.retain v
          (fun c => Prediction.groupedCoefficient L.parent (L.coefficient W) p c •
            (val (L.point c) - b)) (by
              intro c hc
              simp [Prediction.groupedCoefficient, L.coefficient_discarded W c hc]))
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hwp : T.parent k w = p <;> by_cases hwv : w < v <;>
        simp [Prediction.groupedCoefficient, L.parent_retain,
          L.coefficient_retain, retainedPoint, hwp, hwv]

/-- The actual ideal weighted child average is exactly the earlier-candidate
residual point, before any nonlinear parent map is applied. -/
theorem ideal_child_average_eq_residualPoint (W : WeightedTree T)
    (v : T.Node (k + 1)) (val : Y → X) (b : X) (p : T.Node k) :
    (∑ w ∈ Finset.univ.filter (fun w => T.parent k w = p),
      W.weight k w • (if w < v then val (L.retainedPoint w) else b)) =
      Prediction.residualPoint (L.earlierParent v)
        (fun c => val (L.earlierPoint v c)) b (L.actualTheta W v) p := by
  classical
  rw [Prediction.residualPoint, L.actualTheta_correction W v val b p]
  calc
    _ = (∑ w ∈ Finset.univ.filter (fun w => T.parent k w = p),
          W.weight k w • b) +
        ∑ w ∈ Finset.univ.filter (fun w => T.parent k w = p),
          if w < v then W.weight k w • (val (L.retainedPoint w) - b) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hwv : w < v
      · simp only [hwv, ite_true, smul_sub]
        abel
      · simp [hwv]
    _ = _ := by
      rw [← Finset.sum_smul, W.weight_sum k p, one_smul]

end AffineIdentity
end CandidateLedger
end ReflexiveFixedPoints

end

end OAI
