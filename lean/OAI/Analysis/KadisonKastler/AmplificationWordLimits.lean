import OAI.Analysis.KadisonKastler.PhaseCoefficientLimits
import OAI.Analysis.KadisonKastler.PhaseWordDrift

namespace OAI

/-! # Root-mean-square drift of the randomized unitary words -/

namespace KadisonKastler

open Filter
open scoped BigOperators

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k q : ℕ} [NeZero n] [NeZero k] [NeZero q]
local instance wordLimitSourceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance wordLimitSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance wordLimitOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance wordLimitOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance wordLimitMatrixOrder :
    PartialOrder (Algebra (matrixVonNeumann (ι := Fin n) M)) := CStarAlgebra.spectralOrder _
local instance wordLimitMatrixStarOrder :
    StarOrderedRing (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  CStarAlgebra.spectralOrderedRing _

variable {B : Type v} [CStarAlgebra B] {σ : FaithfulTracialState B} {ω : Ultrafilter ℕ}
variable (τ : FaithfulTracialState (Algebra M))
variable (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
variable (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
variable (w : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
variable (hτ : FiniteVectorTrace τ)
variable (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
variable (hFock : PublishedDiagonalFockRepresentation.{v})
variable (hfree : FreeHaarMoments σ R.constant.range
  (Unitary.map (StarMonoidHom.ofClass R.quotient) w))
variable (r : ℕ) (hrk : r + 1 ≤ k) (hrq : r + 1 < q)
variable (hword : freeWordThreshold (r + 1) ≤ n * k)
variable (hthrough : ∀ a : Fin (n * k),
  (∑ s : ThroughLabel a (r + 1), projectionWordWeight (freeWordC (r + 1)) s.val ^ 2) ≤ 64)
variable (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
variable (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)

include hτ hCyclic hFock hfree hrk hrq hword hthrough hδ hb in
/-- The negative randomized word has eventual drift at most `66δ`. -/
theorem negative_amplification_word_limit (z : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      finiteRMS (fun θ : Fin (n * k) → ZMod q =>
        (T * (((star ((w : BoundedSequence _) j) *
          star (diagonalPhase (amplificationPartition E) θ)) ^ (r + 1)).val) -
        (((star ((w : BoundedSequence _) j) *
          star (diagonalPhase (amplificationPartition E) θ)) ^ (r + 1)).val) * T) z) ≤
            66 * δ * ‖z‖ + ε := by
  intro ε hε
  filter_upwards [negative_amplification_coefficient_limit R E w
    (matrixVonNeumannTrace_finiteVector M τ hτ) hCyclic r hrk
    hthrough h hδ hb hFock (amplificationPartition_trace E τ) hfree hword z ε hε] with j hj
  dsimp only at hj ⊢
  have heq := negative_phase_word_drift (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype
    (hilbertMatrix (diagonalAmplification (n := Fin n) h)) z
    (amplificationPartition E) ((w : BoundedSequence _) j) r hrq
  simp only [StarSubalgebra.subtype_apply] at heq
  rw [heq]
  simpa only [negativePhaseCoefficientSequence_apply] using hj

include hτ hCyclic hFock hfree hrk hrq hword hthrough hδ hb in
/-- The positive randomized word has eventual drift `68δ` on the moving vector. -/
theorem positive_amplification_word_limit
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (hs : ∀ j, let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
        ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ)
    (y : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      finiteRMS (fun θ : Fin (n * k) → ZMod q =>
        (T * (((diagonalPhase (amplificationPartition E) θ *
          ((w : BoundedSequence _) j)) ^ r * diagonalPhase (amplificationPartition E) θ).val) -
        (((diagonalPhase (amplificationPartition E) θ *
          ((w : BoundedSequence _) j)) ^ r * diagonalPhase (amplificationPartition E) θ).val) * T)
          (((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val y)) ≤
            68 * δ * ‖y‖ + ε := by
  have hbound := (amplificationPhaseCoefficients_quotient_bounds R E w hFock
    (amplificationPartition_trace E τ) hfree r hword).1
  intro ε hε
  filter_upwards [positive_amplification_coefficient_limit_of_bounds R E w
    (matrixVonNeumannTrace_finiteVector M τ hτ) hCyclic
    r hrk hthrough h hδ hb hbound s hs y ε hε] with j hj
  dsimp only at hj ⊢
  have heq := positive_phase_word_drift (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype
    (hilbertMatrix (diagonalAmplification (n := Fin n) h))
    (((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val y)
    (amplificationPartition E) ((w : BoundedSequence _) j) r hrq
  simp only [StarSubalgebra.subtype_apply] at heq
  rw [heq]
  simpa only [positivePhaseCoefficientSequence_apply] using hj

end

end KadisonKastler

end OAI
