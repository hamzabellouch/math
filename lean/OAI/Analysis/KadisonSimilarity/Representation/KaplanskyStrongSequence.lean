import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyDischarge
import OAI.Analysis.KadisonSimilarity.Representation.FieldWeakClosure
import OAI.Analysis.KadisonSimilarity.Representation.IntertwinerExtension

namespace OAI

/-! # Sequential Kaplansky approximation on a separable Hilbert space

Finite-vector Kaplansky approximation applied to increasing finite sets of
dense vectors gives an actual strongly convergent sequence. Every source
term satisfies the exact norm bound of the target operator.
-/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology CStarAlgebra

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Every member of a represented bicommutant is a strong sequential limit
of source elements, with the exact source norm bound preserved. -/
theorem kaplansky_strong_sequence
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) :
    ∃ a : ℕ → A, (∀ n, ‖a n‖ ≤ ‖T‖) ∧
      ∀ x : H, Tendsto (fun n => σ (a n) x) atTop (𝓝 (T x)) := by
  classical
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let d := TopologicalSpace.denseSeq H
  have hex (n : ℕ) : ∃ a : A, ‖a‖ ≤ ‖T‖ ∧
      ∀ x ∈ (Finset.range (n + 1)).image d, ‖σ a x - T x‖ < 1 / (n + 1 : ℝ) :=
    kaplansky_finite_approximation σ T hT _ _ (by positivity)
  choose a hnorm hclose using hex
  refine ⟨a, hnorm, ?_⟩
  apply strong_tendsto_of_bounded_dense_columns (fun n => σ (a n)) T ‖T‖
    (fun n => (NonUnitalStarAlgHom.norm_apply_le σ (a n)).trans (hnorm n))
  intro j
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop j] with n hn
  apply (hclose n (d j) _).le
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [TopologicalSpace.SeparableSpace H] in
/-- Strong convergence survives extension by zero to the common L² model. -/
theorem isometricExtension_strong_tendsto
    (J : H →ₗᵢ[ℂ] K) (T : ℕ → H →L[ℂ] H) (S : H →L[ℂ] H)
    (hstrong : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 (S x))) :
    ∀ y : K, Tendsto (fun n => isometricExtension J (T n) y) atTop
      (𝓝 (isometricExtension J S y)) := by
  intro y
  change Tendsto (fun n => J (T n (J.toContinuousLinearMap.adjoint y))) atTop
    (𝓝 (J (S (J.toContinuousLinearMap.adjoint y))))
  exact (J.continuous.tendsto _).comp (hstrong _)

end KadisonSimilarity

end

end OAI
