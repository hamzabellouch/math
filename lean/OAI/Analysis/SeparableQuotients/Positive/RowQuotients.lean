import OAI.Analysis.SeparableQuotients.Positive.RowEvaluation
import OAI.Analysis.SeparableQuotients.Positive.ContinuumMeasure
import OAI.Analysis.SeparableQuotients.Positive.RealAdjoint

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal
universe u

namespace SeparableQuotient.Positive.Rows
attribute [local instance] dualSubmoduleNormedGroup dualSubmoduleNormedSpace
open scoped BigOperators
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


def HasSeparableQuotient (𝕜 : Type) [RCLike 𝕜] (X : Type u)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∃ (Y : Type u) (g : NormedAddCommGroup Y),
    letI := g
    ∃ s : NormedSpace 𝕜 Y,
      letI := s
      CompleteSpace Y ∧ SeparableSpace Y ∧ ¬ FiniteDimensional 𝕜 Y ∧
        ∃ T : X →L[𝕜] Y, Function.Surjective T




theorem quotient_of_small_dense_rows
    (μ : Measure ContinuumIndex) [IsProbabilityMeasure μ]
    (hadd : ContinuumAdditive μ) (hsingle : ∀ i, μ {i} = 0)
    (E : Submodule ℝ (StrongDual ℝ X)) (hE : IsClosed (E : Set (StrongDual ℝ X)))
    (u : ∀ n : ℕ, Fin (16 ^ (n+1)) → E)
    (hlo : ∀ n (c : Fin (16 ^ (n+1)) → ℝ),
      Real.sqrt (∑ j, (c j)^2) ≤ ‖∑ j, c j • u n j‖)
    (hhi : ∀ n (c : Fin (16 ^ (n+1)) → ℝ),
      ‖∑ j, c j • u n j‖ ≤ 2 * Real.sqrt (∑ j, (c j)^2))
    (D : ℕ → Finset X) (hD : ∀ m d, d ∈ D m → ‖d‖ ≤ 1)
    (hnorm : ∀ m (v : StrongDual ℝ X),
      v ∈ Submodule.span ℝ {w | ∃ n, n < m ∧ ∃ j, (u n j : StrongDual ℝ X) = w} →
        ∃ d ∈ D m, ‖v‖ ≤ 2 * |v d|)
    (hann : ∀ m n, m ≤ n → ∀ j d, d ∈ D m → (u n j : StrongDual ℝ X) d = 0)
    (A : Set (StrongDual ℝ E)) (hcard : Cardinal.mk A < Cardinal.continuum.{u})
    (hunit : ∀ y ∈ A, ‖y‖ ≤ 1)
    (hdense : evaluation E '' Metric.closedBall (0 : X) 1 ⊆ closure A) :
    HasSeparableQuotient ℝ X := by
  obtain ⟨j, hj⟩ := select_rows_from_small_set μ hadd hsingle u hhi A hcard hunit
  let g (n : ℕ) : E := u n (j n)
  let f (n : ℕ) : StrongDual ℝ X := g n
  have hf (n : ℕ) : (1 : ℝ) ≤ ‖f n‖ := by
    have hh := hlo n (Pi.single (j n) (1 : ℝ))
    simpa [f, g, Pi.single_apply] using hh
  have hn m (v : StrongDual ℝ X)
      (hv : v ∈ Submodule.span ℝ (f '' (Finset.range m : Set ℕ))) :
      ∃ d ∈ D m, ‖v‖ ≤ 2 * |v d| := by
    apply hnorm m v
    apply Submodule.span_mono (t := {w | ∃ n, n < m ∧ ∃ j, (u n j : StrongDual ℝ X) = w}) _ hv
    rintro w ⟨n, hn, rfl⟩
    exact ⟨n, Finset.mem_range.mp hn, j n, rfl⟩
  have han m n (hmn : m ≤ n) d (hd : d ∈ D m) : f n d = 0 :=
    hann m n hmn (j n) d hd
  have hp := prefixBound_of_half_normers f D hD hn han
  have hrange := eval_range_of_dense_summable E hE g hp (by norm_num : (0:ℝ) < 1) hf A hdense hj
  obtain ⟨hsurj, hsep, hinf⟩ :=
    prefix_evaluation_surjective f (by norm_num : (0:ℝ) < 1) hf D hD hn han hrange
  refine ⟨ClosedSpan (prefixCoord f), inferInstance, inferInstance, inferInstance, hsep, hinf, ?_⟩
  exact ⟨(evaluation (ClosedSpan f)).codRestrict (ClosedSpan (prefixCoord f)) hrange, hsurj⟩

end SeparableQuotient.Positive.Rows

end

end

end OAI
