import OAI.Analysis.KadisonKastler.HilbertSumCorners
import OAI.Analysis.KadisonKastler.CountableConjugacyAssembly

namespace OAI

/-! # Block decomposition from central coordinate projections

Commutation with the coordinate projections gives the diagonal blocks.
Conversely, a uniformly bounded family of corner operators belongs to the
original algebra by the bicommutant theorem, without a normality assumption.
-/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

theorem blockAlgebraDecomposition_of_central_coordinates (M : VonNeumannAlgebra (lp E 2))
    (hQ : ∀ n, hilbertSumProjection n ∈ M ∧ hilbertSumProjection n ∈ M.commutant) :
    BlockAlgebraDecomposition
      (fun n => isometricCornerAlgebra (hilbertSumInclusion (E := E) n) M (hQ n).1) M := by
  constructor
  · intro T hT
    refine ⟨fun n => hilbertSumCompression n T,
      fun n => hilbertSumCompression_norm_le n T,
      fun n => hilbertSumCompression_mem_corner M n (hQ n).1 T hT, ?_⟩
    intro f n
    exact hilbertSum_diagonal_of_commutes T
      (fun i => ((VonNeumannAlgebra.mem_commutant_iff.mp (hQ i).2) T hT).symm) f n
  · intro F C hC hFn hFM
    let T := hilbertSumOperator F C hC hFn
    refine ⟨T, ?_, fun _ _ => hilbertSumOperator_apply F C hC hFn _ _⟩
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro S hS
    have hSd (f : lp E 2) (n : ℕ) : S f n = hilbertSumCompression n S (f n) :=
      hilbertSum_diagonal_of_commutes S
        (fun i => (VonNeumannAlgebra.mem_commutant_iff.mp hS) _ (hQ i).1) f n
    have hcomm (n : ℕ) (v : E n) :
        F n (hilbertSumCompression n S v) = hilbertSumCompression n S (F n v) := by
      exact hilbertSum_corner_commutes M n (hQ n).1 (F n) (hFM n) S hS v
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    change S (T f) n = T (S f) n
    change S (hilbertSumOperator F C hC hFn f) n = hilbertSumOperator F C hC hFn (S f) n
    simp only [hSd, hilbertSumOperator_apply]
    exact (hcomm n (f n)).symm

end

end KadisonKastler

end OAI
