import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-! # Countable strong-operator tests for commutation

On a uniformly bounded set of operators, convergence on a countable dense
set of vectors implies convergence on every vector. A countable dense set
of coordinate sequences therefore supplies all commutant tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Uniform contraction bounds extend pointwise convergence from a dense
sequence to every vector. -/
theorem tendsto_apply_of_dense_contractions (v : ℕ → H) (hv : DenseRange v)
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hA : ∀ n, ‖A n‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (h : ∀ j, Tendsto (fun n => A n (v j)) atTop (𝓝 (B (v j)))) (x : H) :
    Tendsto (fun n => A n x) atTop (𝓝 (B x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := hv.exists_dist_lt x (by positivity : 0 < ε / 4)
  have hA' (n : ℕ) (y : H) : ‖A n y‖ ≤ ‖y‖ := by
    apply ((A n).le_opNorm y).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hA n) (norm_nonneg y)
  have hB' (y : H) : ‖B y‖ ≤ ‖y‖ := by
    apply (B.le_opNorm y).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (norm_nonneg y)
  filter_upwards [(Metric.tendsto_nhds.mp (h j)) (ε / 2) (by positivity)] with n hn
  have ha : dist (A n x) (A n (v j)) ≤ dist x (v j) := by
    simpa only [dist_eq_norm, map_sub] using hA' n (x - v j)
  have hb : dist (B (v j)) (B x) ≤ dist x (v j) := by
    simpa only [dist_eq_norm, map_sub, norm_sub_rev] using hB' (v j - x)
  have ht := (dist_triangle (A n x) (A n (v j)) (B x)).trans
    (add_le_add le_rfl (dist_triangle (A n (v j)) (B (v j)) (B x)))
  linarith

/-- Every contraction-valued set on a separable space has a countable
subset that approximates each of its elements strongly by a sequence. -/
theorem exists_countable_strong_dense_contractions [SeparableSpace H]
    (S : Set (H →L[ℂ] H)) (hS : ∀ T ∈ S, ‖T‖ ≤ 1) :
    ∃ E : Set (H →L[ℂ] H), E.Countable ∧ E ⊆ S ∧
      ∀ T ∈ S, ∃ A : ℕ → H →L[ℂ] H,
        (∀ n, A n ∈ E) ∧ ∀ ξ, Tendsto (fun n => A n ξ) atTop (𝓝 (T ξ)) := by
  obtain ⟨v, hv⟩ := exists_dense_seq (α := H)
  let coordinates : (H →L[ℂ] H) → ℕ → H := fun A n => A (v n)
  obtain ⟨D, hDc, hDsub, hDdense⟩ := exists_countable_dense_subset (coordinates '' S)
  choose lift hliftS hlift using fun z : D => hDsub z.property
  let E : Set (H →L[ℂ] H) := Set.range lift
  have hEc : E.Countable := by
    let := hDc.to_subtype
    exact Set.countable_range lift
  have hES : E ⊆ S := by
    rintro T ⟨z, rfl⟩
    exact hliftS z
  refine ⟨E, hEc, hES, ?_⟩
  intro T hT
  obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp (hDdense ⟨T, hT, rfl⟩)
  let A : ℕ → H →L[ℂ] H := fun n => lift ⟨z n, hz n⟩
  have hAE (n : ℕ) : A n ∈ E := ⟨⟨z n, hz n⟩, rfl⟩
  refine ⟨A, hAE, ?_⟩
  apply tendsto_apply_of_dense_contractions v hv A T
    (fun n => hS (A n) (hES (hAE n))) (hS T hT)
  intro j
  have ht := tendsto_pi_nhds.mp hzt j
  convert ht using 1
  funext n
  exact congrFun (hlift ⟨z n, hz n⟩) j

/-- Commutation with a fixed bounded operator is closed under strong
convergence. -/
theorem commute_of_strong_tendsto (A T : H →L[ℂ] H) (B : ℕ → H →L[ℂ] H)
    (hB : ∀ ξ, Tendsto (fun n => B n ξ) atTop (𝓝 (T ξ)))
    (hcomm : ∀ n, Commute A (B n)) : Commute A T := by
  apply ContinuousLinearMap.ext
  intro ξ
  have hl := (A.continuous.tendsto (T ξ)).comp (hB ξ)
  change Tendsto (fun n => A (B n ξ)) atTop (𝓝 (A (T ξ))) at hl
  have hr := hB (A ξ)
  have he : (fun n => A (B n ξ)) = fun n => B n (A ξ) := by
    funext n
    exact congrArg (fun U : H →L[ℂ] H => U ξ) (hcomm n).eq
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

/-- Countably many operators determine the entire commutant of an
arbitrary contraction-valued set. -/
theorem exists_countable_commutant_tests [SeparableSpace H]
    (S : Set (H →L[ℂ] H)) (hS : ∀ T ∈ S, ‖T‖ ≤ 1) :
    ∃ E : Set (H →L[ℂ] H), E.Countable ∧ E ⊆ S ∧
      ∀ A : H →L[ℂ] H, (∀ T ∈ E, Commute A T) ↔ ∀ T ∈ S, Commute A T := by
  obtain ⟨E, hEc, hES, hE⟩ := exists_countable_strong_dense_contractions S hS
  refine ⟨E, hEc, hES, fun A => ⟨?_, ?_⟩⟩
  · intro hcomm T hT
    obtain ⟨B, hBE, hBT⟩ := hE T hT
    exact commute_of_strong_tendsto A T B hBT (fun n => hcomm (B n) (hBE n))
  · exact fun hcomm T hT => hcomm T (hES hT)

/-- The unit ball of any operator set admits countably many commutant tests. -/
theorem exists_countable_unitBall_commutant_tests [SeparableSpace H]
    (S : Set (H →L[ℂ] H)) :
    ∃ E : Set (H →L[ℂ] H), E.Countable ∧ E ⊆ {T ∈ S | ‖T‖ ≤ 1} ∧
      ∀ A : H →L[ℂ] H, (∀ T ∈ E, Commute A T) ↔ ∀ T ∈ S, ‖T‖ ≤ 1 → Commute A T := by
  simpa only [Set.mem_ofPred_eq, and_imp] using
    exists_countable_commutant_tests {T ∈ S | ‖T‖ ≤ 1} (fun _ h => h.2)

end

end KadisonKastler

end OAI
