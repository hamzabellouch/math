import OAI.Probability.FreeIsing.Estimates.RelabelMeasure
import OAI.Probability.FreeIsing.Spectral.KoopmanInvolutions
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.TreeKoopman

instance labelProbability (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

def reflection {d : ℕ} (c : Fin d) :
    (TreeVertex d → ℝ) → (TreeVertex d → ℝ) :=
  relabel (prefixTreeAut c)

theorem reflection_measurePreserving {d : ℕ} (c : Fin d) :
    MeasurePreserving (reflection c) (labelMeasure d) (labelMeasure d) :=
  measurePreserving_relabel (prefixTreeAut c)

theorem reflection_involutive {d : ℕ} (c : Fin d) :
    Function.Involutive (reflection c) := by
  intro U
  funext v
  change U (prefixFlip c (prefixFlip c v)) = U v
  rw [prefixFlip_twice]

def average (d : ℕ) :
    Lp ℝ 2 (labelMeasure d) →L[ℝ] Lp ℝ 2 (labelMeasure d) :=
  koopmanAverage (fun c : Fin d => reflection c) reflection_measurePreserving

theorem average_selfAdjoint (d : ℕ) : IsSelfAdjoint (average d) :=
  koopmanAverage_selfAdjoint _ _ reflection_involutive

theorem average_norm_le_one {d : ℕ} (hd : 0 < d) : ‖average d‖ ≤ 1 := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  exact koopmanAverage_norm_le_one _ _

def centeredAverage (d : ℕ) :
    centeredL2 (labelMeasure d) →L[ℝ] centeredL2 (labelMeasure d) :=
  centeredKoopmanAverage (fun c : Fin d => reflection c)
    reflection_measurePreserving reflection_involutive

theorem centeredAverage_selfAdjoint (d : ℕ) : IsSelfAdjoint (centeredAverage d) :=
  centeredKoopmanAverage_selfAdjoint _ _ _

theorem centeredAverage_norm_le_one {d : ℕ} (hd : 0 < d) :
    ‖centeredAverage d‖ ≤ 1 := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  exact centeredKoopmanAverage_norm_le_one _ _ _

@[simp] theorem centeredAverage_apply_coe {d : ℕ}
    (f : centeredL2 (labelMeasure d)) :
    (centeredAverage d f : Lp ℝ 2 (labelMeasure d)) = average d f := rfl

@[simp] theorem centeredAverage_pow_apply_coe {d : ℕ}
    (n : ℕ) (f : centeredL2 (labelMeasure d)) :
    ((centeredAverage d ^ n) f : Lp ℝ 2 (labelMeasure d)) =
      (average d ^ n) (f : Lp ℝ 2 (labelMeasure d)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change (average d) (((centeredAverage d ^ n) f : centeredL2 (labelMeasure d)) :
      Lp ℝ 2 (labelMeasure d)) = average d ((average d ^ n) (f : Lp ℝ 2 (labelMeasure d)))
    rw [ih]

theorem reflection_toLp_eq {d : ℕ}
    (Z : (TreeVertex d → ℝ) → (TreeVertex d → ℝ))
    (hZ : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Z (relabel g U) = relabel g (Z U))
    (hLp : ∀ v, MemLp (fun U => Z U v) 2 (labelMeasure d))
    (c : Fin d) (v : TreeVertex d) :
    koopmanL2 (reflection c) (reflection_measurePreserving c)
      ((hLp v).toLp (fun U => Z U v)) =
      (hLp (prefixFlip c v)).toLp (fun U => Z U (prefixFlip c v)) := by
  change Lp.compMeasurePreserving (reflection c) (reflection_measurePreserving c)
    ((hLp v).toLp _) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  filter_upwards [hZ (prefixTreeAut c)] with U hU
  exact congrFun hU v

theorem average_toLp_eq {d : ℕ}
    (Z : (TreeVertex d → ℝ) → (TreeVertex d → ℝ))
    (hZ : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Z (relabel g U) = relabel g (Z U))
    (hLp : ∀ v, MemLp (fun U => Z U v) 2 (labelMeasure d))
    (v : TreeVertex d) :
    average d ((hLp v).toLp (fun U => Z U v)) =
      (d : ℝ)⁻¹ • ∑ c : Fin d,
        (hLp (prefixFlip c v)).toLp (fun U => Z U (prefixFlip c v)) := by
  simp only [average, koopmanAverage, smul_apply, sum_apply,
    Fintype.card_fin]
  congr 1
  exact Finset.sum_congr rfl (fun c _ => reflection_toLp_eq Z hZ hLp c v)

end Problem367.TreeKoopman

end

end OAI
