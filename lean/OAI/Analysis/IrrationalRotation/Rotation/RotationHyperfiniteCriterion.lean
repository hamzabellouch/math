import OAI.Analysis.IrrationalRotation.Operators.HyperfiniteCriterion
import OAI.Analysis.IrrationalRotation.Operators.BicommutantDensity
import OAI.Analysis.IrrationalRotation.Model.Rotation

namespace OAI

noncomputable section
open Filter
open scoped Topology Pointwise

namespace Invariant233.HyperfiniteCriterion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem isHyperfinite_of_generator_approximation
    (s : Set (H →L[ℂ] H)) (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hmono : Monotone A)
    (hinside : ∀ n, A n ≤ (vonNeumannGenerated s).toStarSubalgebra)
    (hfinite : ∀ n, FiniteDimensional ℂ (A n))
    (hs : ∀ T ∈ s, asStrong T ∈ closure {B : H →Lₚₜ[ℂ] H |
      ∃ n, strongOperatorUnderlying B ∈ A n}) :
    IsHyperfinite (vonNeumannGenerated s) := by
  refine ⟨A, hmono, hinside, hfinite, ?_⟩
  rw [strong_union_eq A hmono, BicommutantDensity.strongClosure_eq_bicommutant]
  have hgen := generated_iSup_eq_of_generator_approximation s A hinside hs
  have hset : Set.centralizer (Set.centralizer
      (↑(iSup A) : Set (H →L[ℂ] H))) =
      (vonNeumannGenerated s : Set (H →L[ℂ] H)) := by
    calc
      _ = (vonNeumannGenerated (↑(iSup A) : Set (H →L[ℂ] H)) :
          Set (H →L[ℂ] H)) := by
        symm
        rw [coe_vonNeumannGenerated, StarMemClass.star_coe_eq, Set.union_self]
      _ = _ := congrArg (fun M : VonNeumannAlgebra H => (M : Set (H →L[ℂ] H))) hgen
  simp only [hset, SetLike.mem_coe]

theorem isHyperfinite_of_generator_sequences
    (s : Set (H →L[ℂ] H)) (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hmono : Monotone A)
    (hinside : ∀ n, A n ≤ (vonNeumannGenerated s).toStarSubalgebra)
    (hfinite : ∀ n, FiniteDimensional ℂ (A n))
    (hs : ∀ T ∈ s, ∃ B : ℕ → H →L[ℂ] H,
      (∀ n, B n ∈ A n) ∧ ∀ x, Tendsto (fun n => B n x) atTop (𝓝 (T x))) :
    IsHyperfinite (vonNeumannGenerated s) := by
  apply isHyperfinite_of_generator_approximation s A hmono hinside hfinite
  intro T hT
  obtain ⟨B, hB, hlim⟩ := hs T hT
  exact mem_strong_union_closure_of_tendsto A B T hB hlim

end Invariant233.HyperfiniteCriterion

namespace Invariant233.Rotation

theorem isHyperfinite_of_strong_generator_sequences
    (θ : ℝ) (A : ℕ → StarSubalgebra ℂ (Hilbert →L[ℂ] Hilbert))
    (hmono : Monotone A) (hinside : ∀ n, A n ≤ (algebra θ).toStarSubalgebra)
    (hfinite : ∀ n, FiniteDimensional ℂ (A n))
    (u v : ℕ → Hilbert →L[ℂ] Hilbert)
    (hu : ∀ n, u n ∈ A n) (hv : ∀ n, v n ∈ A n)
    (hU : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (U x)))
    (hV : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (V θ x))) :
    IsHyperfinite (algebra θ) := by
  apply HyperfiniteCriterion.isHyperfinite_of_generator_sequences
    ({U, V θ} : Set (Hilbert →L[ℂ] Hilbert)) A hmono hinside hfinite
  intro T hT
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
  rcases hT with rfl | rfl
  · exact ⟨u, hu, hU⟩
  · exact ⟨v, hv, hV⟩

end Invariant233.Rotation

end

end OAI
