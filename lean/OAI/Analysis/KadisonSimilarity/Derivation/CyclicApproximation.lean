import OAI.Analysis.KadisonSimilarity.Derivation.CyclicFactorization
import OAI.Analysis.KadisonSimilarity.Similarity.CompletelyBoundedImplementation
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-!
# Approximate cyclic columns

Standard-form vector realization and matrix Kaplansky density with quotient
norm lifting give uniformly bounded approximating columns.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology Pointwise

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder A] [StarOrderedRing A]

/-- The commutant of an operator star subalgebra, bundled as a von Neumann
algebra by the elementary triple-commutant identity. -/
def starSubalgebraCommutant (N : StarSubalgebra ℂ (K →L[ℂ] K)) : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (N : Set (K →L[ℂ] K))
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

@[simp] theorem coe_starSubalgebraCommutant (N : StarSubalgebra ℂ (K →L[ℂ] K)) :
    (starSubalgebraCommutant N : Set (K →L[ℂ] K)) = Set.centralizer (N : Set (K →L[ℂ] K)) := by
  change Set.centralizer ((N : Set (K →L[ℂ] K)) ∪ star (N : Set (K →L[ℂ] K))) = _
  rw [StarMemClass.star_coe_eq, Set.union_self]

/-- The bicommutant σ(A)″ of the represented C-star algebra. -/
def representationVonNeumannAlgebra (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : VonNeumannAlgebra K :=
  (starSubalgebraCommutant σ.range).commutant

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem coe_representationVonNeumannAlgebra (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (representationVonNeumannAlgebra σ : Set (K →L[ℂ] K)) =
      Set.centralizer (Set.centralizer (σ.range : Set (K →L[ℂ] K))) := by
  simp [representationVonNeumannAlgebra]

omit [PartialOrder A] [StarOrderedRing A] in
theorem mem_representationVonNeumannAlgebra (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : A) :
    σ a ∈ representationVonNeumannAlgebra σ := by
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra]
  exact Set.subset_centralizer_centralizer ⟨a, rfl⟩

/-- The standard-form vector-realization property of a cyclic representation.
It is the consequence of Haagerup (1975), Lemma 2.10(1), pp. 278–279, applied
to the commutant on the cyclic subspace of a separating vector. -/
def HaagerupCyclicVectorRealization (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ n : ℕ, ∀ ξ : HilbertCopies K n, ‖ξ‖ = 1 →
    ∃ ζ : K, ‖ζ‖ = 1 ∧
      VectorQuadraticFormsAgree (representationVonNeumannAlgebra σ).commutant.toStarSubalgebra ξ ζ

/-- The matrix-column consequence of Kaplansky density (Blackadar, I.9.1.3),
together with the C-star first isomorphism theorem and quotient norm lifting.
The lifting bound has fixed slack 2. -/
def KaplanskyColumnApproximation (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ n : ℕ, ∀ V : K →L[ℂ] HilbertCopies K n, ‖V‖ ≤ 1 →
    (∀ i : Fin n, columnEntry V i ∈ representationVonNeumannAlgebra σ) →
    ∀ ζ : K, ∀ ε : ℝ, 0 < ε →
      ∃ W : Matrix (Fin n) (Fin 1) A,
        ‖CStarMatrix.ofMatrix W‖ ≤ 2 ∧ ‖columnAction σ W ζ - V ζ‖ < ε

/-- Pointwise approximation with arbitrary positive errors supplies a sequence
of columns with the same norm bound. -/
theorem exists_approximating_column_sequence
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (kaplansky : KaplanskyColumnApproximation σ)
    {n : ℕ} (V : K →L[ℂ] HilbertCopies K n) (hV : ‖V‖ ≤ 1)
    (hentry : ∀ i : Fin n, columnEntry V i ∈ representationVonNeumannAlgebra σ)
    (ζ : K) :
    ∃ W : ℕ → Matrix (Fin n) (Fin 1) A,
      (∀ j, ‖CStarMatrix.ofMatrix (W j)‖ ≤ 2) ∧
      Tendsto (fun j => columnAction σ (W j) ζ) atTop (𝓝 (V ζ)) := by
  have happ (j : ℕ) : ∃ W : Matrix (Fin n) (Fin 1) A,
      ‖CStarMatrix.ofMatrix W‖ ≤ 2 ∧
      ‖columnAction σ W ζ - V ζ‖ < 1 / ((j : ℝ) + 1) :=
    kaplansky n V hV hentry ζ _ (by positivity)
  choose W hW herr using happ
  refine ⟨W, hW, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun j => norm_nonneg _) (fun j => (herr j).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Vector realization and Kaplansky approximation imply approximate cyclic
column factorization. -/
theorem approximateCyclicColumns_of_published_inputs
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (haagerup : HaagerupCyclicVectorRealization σ)
    (kaplansky : KaplanskyColumnApproximation σ) : ApproximateCyclicColumns σ := by
  intro n ξ hξ
  obtain ⟨ζ, hζ, hforms⟩ := haagerup n ξ hξ
  obtain ⟨V, hV, hVζ, hentry⟩ :=
    exists_column_factorization_of_vector_realization (representationVonNeumannAlgebra σ) ξ ζ hforms
  obtain ⟨W, hW, ht⟩ := exists_approximating_column_sequence σ kaplansky V hV hentry ζ
  refine ⟨ζ, hζ, W, hW, ?_⟩
  simpa only [hVζ] using ht

/-- A cyclic derivation is implemented with a uniform norm bound under
Dickson's estimate, vector realization, Kaplansky approximation and Paulsen similarity. -/
theorem cyclic_derivation_implementation_of_published_inputs
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (dickson : DicksonTwoBound (A := A) (RectangularSum F K))
    (haagerup : HaagerupCyclicVectorRealization σ)
    (kaplansky : KaplanskyColumnApproximation σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ δ hδ)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖ :=
  cyclic_derivation_implementation ρ σ δ hδ dickson
    (approximateCyclicColumns_of_published_inputs σ haagerup kaplansky) paulsen

end KadisonSimilarity

end

end OAI
