import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.ExtensionLaw

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Filter
open scoped Topology

lemma restrictionLaw_bad {s d n : ℕ} {X : Type*} [LinearOrder X]
    (e : Fin n ↪o X) (μ : ProbabilityMeasure (ListPattern s d X)) :
    (restrictionLaw e μ) {D | ¬GoodPatternOn D Finset.univ} =
      μ {C | ¬GoodPatternOn (C.restrict e) Finset.univ} := by
  exact ProbabilityMeasure.map_apply _
    (ListPattern.measurable_restrict e).aemeasurable MeasurableSet.of_discrete

theorem homogeneous_bad_finite_law {s d : ℕ} {ξ : ℝ}
    (hcounter : ∀ r, s ≤ r → ∃ μ : ProbabilityMeasure (ListPattern s d (Fin r)),
      ∀ e : Fin s ↪o Fin r,
        ξ ≤ (μ {C | ¬GoodPatternOn (C.restrict e) Finset.univ} : ℝ))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ProbabilityMeasure (ListPattern s d (Fin k)),
      (∀ n, n ≤ k → ∀ e f : Fin n ↪o Fin k,
        dist (restrictionLaw e μ) (restrictionLaw f μ) < ε) ∧
      (∀ e : Fin s ↪o Fin k,
        ξ ≤ (μ {C | ¬GoodPatternOn (C.restrict e) Finset.univ} : ℝ)) := by
  classical
  have (n : ℕ) : CompactSpace (ProbabilityMeasure (ListPattern s d (Fin n))) :=
    instCompactSpaceProbabilityMeasure
  obtain ⟨r, hr, hram⟩ := compact_simultaneous_ramsey
    (fun n => ProbabilityMeasure (ListPattern s d (Fin n))) (k + 1) k ε hε
  let N := max r s
  obtain ⟨ν, hν⟩ := hcounter N (le_max_right _ _)
  let ν' := extensionLaw (Finset.range N) (Finset.card_range N) ν
  let f (n : ℕ) (S : Finset ℕ) : ProbabilityMeasure (ListPattern s d (Fin n)) :=
    if h : S.card = n then restrictionLaw (S.orderEmbOfFin h) ν'
    else restrictionLaw (Fin.valOrderEmb n) ν'
  obtain ⟨K, hKH, hK, hhom⟩ := hram (Finset.range N)
    (by simp only [Finset.card_range]; exact le_max_left _ _) f
  let ι := K.orderEmbOfFin hK
  let μ := restrictionLaw ι ν'
  have hf {n : ℕ} (e : Fin n ↪o ℕ) :
      f n (Finset.univ.map e.toEmbedding) = restrictionLaw e ν' := by
    simp only [f, Finset.card_map, Finset.card_univ, Fintype.card_fin, dite_eq_left]
    rw [finite_embedding_sorted]
  refine ⟨μ, ?_, ?_⟩
  · intro n hn e g
    have hsub (e : Fin n ↪o Fin k) :
        Finset.univ.map (e.trans ι).toEmbedding ⊆ K := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
      exact K.orderEmbOfFin_mem hK (e j)
    have hh := hhom n (by omega)
      (Finset.univ.map (e.trans ι).toEmbedding) (hsub e) (by simp)
      (Finset.univ.map (g.trans ι).toEmbedding) (hsub g) (by simp)
    rw [hf, hf] at hh
    simpa only [μ, restrictionLaw_comp] using hh
  · intro e
    have he : ∀ i, (e.trans ι) i ∈ Finset.range N :=
      fun i => hKH (K.orderEmbOfFin_mem hK (e i))
    have h := hν (embeddingInside (Finset.range N) (Finset.card_range N) (e.trans ι) he)
    rw [← restrictionLaw_bad] at h ⊢
    change ξ ≤ ((restrictionLaw e (restrictionLaw ι ν'))
      {D | ¬GoodPatternOn D Finset.univ} : ℝ)
    rw [restrictionLaw_comp]
    change ξ ≤ ((restrictionLaw (e.trans ι)
      (extensionLaw (Finset.range N) (Finset.card_range N) ν))
      {D | ¬GoodPatternOn D Finset.univ} : ℝ)
    rw [restriction_extensionLaw_inside _ _ _ he]
    exact h

end LargeIndependentSets

end OAI
