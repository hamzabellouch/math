import OAI.Analysis.KadisonKastler.AmplificationWordLimits
import OAI.Analysis.KadisonKastler.AmplificationWordUnits
import OAI.Analysis.KadisonKastler.ControlledPowerDrift

namespace OAI

/-! # The randomized power errors from the coefficient word estimates

The positive power restores the controlled final factor, costing `2δ`.
The negative power is already the negative word.  Thus both actual powers
satisfy the `70δ` bound used in the recovery rows.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators

noncomputable section

universe u v

variable {A : Type*} [CStarAlgebra A]

/-- Evaluation commutes with appending a constant unitary. -/
theorem sequenceUnitaryEval_mul_constant
    (s : unitary (BoundedSequence A)) (U : unitary A) (j : ℕ) :
    sequenceUnitaryEval
      (s * Unitary.map (StarMonoidHom.ofClass (boundedSequenceConst (B := A))) U) j =
        sequenceUnitaryEval s j * U := by
  apply Subtype.ext
  rfl

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k q : ℕ} [NeZero n] [NeZero k] [NeZero q]
local instance powerLimitSourceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance powerLimitSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance powerLimitOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance powerLimitOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance powerLimitMatrixOrder :
    PartialOrder (Algebra (matrixVonNeumann (ι := Fin n) M)) := CStarAlgebra.spectralOrder _
local instance powerLimitMatrixStarOrder :
    StarOrderedRing (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  CStarAlgebra.spectralOrderedRing _

variable {B : Type v} [CStarAlgebra B] {σ : FaithfulTracialState B} {ω : Ultrafilter ℕ}
variable (τ : FaithfulTracialState (Algebra M))
variable (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
variable (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
variable (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
variable (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
variable (hτ : FiniteVectorTrace τ)
variable (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
variable (hFock : PublishedDiagonalFockRepresentation.{v})
variable (hfree : FreeHaarMoments σ R.constant.range
  (Unitary.map (StarMonoidHom.ofClass R.quotient) s))
variable (r : ℕ) (hrk : r + 1 ≤ k) (hrq : r + 1 < q)
variable (hword : freeWordThreshold (r + 1) ≤ n * k)
variable (hthrough : ∀ a : Fin (n * k),
  (∑ t : ThroughLabel a (r + 1), projectionWordWeight (freeWordC (r + 1)) t.val ^ 2) ≤ 64)
variable (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
variable (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)

include hτ hCyclic hFock hfree hrk hrq hword hthrough hδ hb in
/-- Actual adjoint powers have eventual root-mean-square error at most `70δ`. -/
theorem negative_amplification_power_limit (ξ : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H :=
        hilbertMatrix (diagonalAmplification (n := Fin n) h)
      finiteRMS (fun θ : Fin (n * k) → ZMod q =>
        T ((star ((phaseWordBase E (sequenceUnitaryEval s j * U) θ :
          Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r + 1))).val ξ) -
        (star ((phaseWordBase E (sequenceUnitaryEval s j * U) θ :
          Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r + 1))).val (T ξ)) ≤
            70 * δ * ‖ξ‖ + ε := by
  let w := s * Unitary.map
    (StarMonoidHom.ofClass (boundedSequenceConst
      (B := Algebra (matrixVonNeumann (ι := Fin n) M)))) U
  have hw : FreeHaarMoments σ R.constant.range
      (Unitary.map (StarMonoidHom.ofClass R.quotient) w) :=
    freeHaar_mul_constant_right R.quotient s hfree U
  intro ε hε
  filter_upwards [negative_amplification_word_limit τ R E w hτ hCyclic hFock hw
    r hrk hrq hword hthrough h hδ hb ξ ε hε] with j hj
  dsimp only at hj ⊢
  have heq (θ : Fin (n * k) → ZMod q) :
      star ((phaseWordBase E (sequenceUnitaryEval s j * U) θ :
        Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r + 1)) =
      (star ((w : BoundedSequence _) j) *
        star (diagonalPhase (amplificationPartition E) θ)) ^ (r + 1) := by
    change star ((diagonalPhase (amplificationPartition E) θ *
      (((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j) *
        (U : Algebra (matrixVonNeumann (ι := Fin n) M)))) ^ (r + 1)) = _
    rw [star_pow, star_mul]
    rfl
  simp_rw [heq]
  have hconvert : finiteRMS (fun θ : Fin (n * k) → ZMod q =>
      (hilbertMatrix (diagonalAmplification (n := Fin n) h) *
        ((star ((w : BoundedSequence _) j) *
          star (diagonalPhase (amplificationPartition E) θ)) ^ (r + 1)).val -
        ((star ((w : BoundedSequence _) j) *
          star (diagonalPhase (amplificationPartition E) θ)) ^ (r + 1)).val *
          hilbertMatrix (diagonalAmplification (n := Fin n) h)) ξ) ≤
      70 * δ * ‖ξ‖ + ε := hj.trans (by nlinarith [mul_nonneg hδ (norm_nonneg ξ)])
  simpa only [sub_apply, mul_apply_eq_comp] using hconvert

include hτ hCyclic hFock hfree hrk hrq hword hthrough hδ hb in
/-- Restoring the controlled final unitary turns the `68δ` word estimate
into the actual positive-power estimate `70δ`. -/
theorem positive_amplification_power_limit
    (hs : ∀ j, let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
        ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ)
    (ξ : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H :=
        hilbertMatrix (diagonalAmplification (n := Fin n) h)
      finiteRMS (fun θ : Fin (n * k) → ZMod q =>
        T (((phaseWordBase E (sequenceUnitaryEval s j * U) θ :
          Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r + 1)).val ξ) -
        ((phaseWordBase E (sequenceUnitaryEval s j * U) θ :
          Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r + 1)).val
            ((star U.val.val) (T (U.val.val ξ)))) ≤ 70 * δ * ‖ξ‖ + ε := by
  let w := s * Unitary.map
    (StarMonoidHom.ofClass (boundedSequenceConst
      (B := Algebra (matrixVonNeumann (ι := Fin n) M)))) U
  have hw : FreeHaarMoments σ R.constant.range
      (Unitary.map (StarMonoidHom.ofClass R.quotient) w) :=
    freeHaar_mul_constant_right R.quotient s hfree U
  let ρ : Algebra (matrixVonNeumann (ι := Fin n) M) →⋆ₐ[ℂ]
      (Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) :=
    (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype
  let Uop : unitary (Generator.FiniteHilbert (Fin n) H →L[ℂ]
      Generator.FiniteHilbert (Fin n) H) := Unitary.map (StarMonoidHom.ofClass ρ) U
  let sop : ℕ → unitary (Generator.FiniteHilbert (Fin n) H →L[ℂ]
      Generator.FiniteHilbert (Fin n) H) :=
    fun j => Unitary.map (StarMonoidHom.ofClass ρ) (sequenceUnitaryEval s j)
  let Q : ℕ → (Fin (n * k) → ZMod q) →
      unitary (Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) :=
    fun j θ => Unitary.map (StarMonoidHom.ofClass ρ)
      (positivePhaseWordUnitary E (sequenceUnitaryEval w j) r θ)
  let T : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H :=
    hilbertMatrix (diagonalAmplification (n := Fin n) h)
  have hQ (j : ℕ) (θ : Fin (n * k) → ZMod q) :
      (Q j θ : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) =
        (((diagonalPhase (amplificationPartition E) θ * ((w : BoundedSequence _) j)) ^ r *
          diagonalPhase (amplificationPartition E) θ).val) :=
    congrArg Subtype.val (positivePhaseWordUnitary_coe E (sequenceUnitaryEval w j) r θ)
  have hsop (j : ℕ) :
      (sop j : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) =
        ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val := rfl
  have hUop :
      (Uop : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) =
        U.val.val := rfl
  have hwordOp : ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      finiteRMS (fun θ =>
        (T * (Q j θ : Generator.FiniteHilbert (Fin n) H →L[ℂ]
          Generator.FiniteHilbert (Fin n) H) -
          (Q j θ : Generator.FiniteHilbert (Fin n) H →L[ℂ]
            Generator.FiniteHilbert (Fin n) H) * T)
          ((sop j : Generator.FiniteHilbert (Fin n) H →L[ℂ]
            Generator.FiniteHilbert (Fin n) H) (Uop.val ξ))) ≤
          68 * δ * ‖ξ‖ + ε := by
    intro ε hε
    filter_upwards [positive_amplification_word_limit τ R E w hτ hCyclic hFock hw
      r hrk hrq hword hthrough h hδ hb s hs (Uop.val ξ) ε hε] with j hj
    dsimp only at hj
    rw [Unitary.norm_map] at hj
    simpa only [hQ, T, hsop] using hj
  have hproduct (j : ℕ) (θ : Fin (n * k) → ZMod q) :
      (Q j θ : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) *
        (sop j : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) *
        (Uop : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) =
      ((phaseWordBase E (sequenceUnitaryEval s j * U) θ :
        Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r + 1)).val := by
    have ht := congrArg
      (fun v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)) => v.val.val)
      (positivePhaseWordUnitary_mul E (sequenceUnitaryEval w j) r θ)
    simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow] at ht
    rw [show sequenceUnitaryEval w j = sequenceUnitaryEval s j * U from
      sequenceUnitaryEval_mul_constant s U j] at ht
    change (Q j θ : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) *
      ((sop j : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) * (Uop : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H)) = _ at ht
    change _ = ρ ((phaseWordBase E (sequenceUnitaryEval s j * U) θ :
      Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r + 1))
    rw [map_pow]
    simpa only [mul_assoc, ρ, StarSubalgebra.subtype_apply] using ht
  intro ε hε
  filter_upwards [eventually_controlled_word_error (ω : Filter ℕ) T Q sop Uop ξ hδ hs
    hwordOp ε hε] with j hj
  dsimp only
  simp only [hproduct] at hj
  simpa only [T, hUop] using hj

end

end KadisonKastler

end OAI
