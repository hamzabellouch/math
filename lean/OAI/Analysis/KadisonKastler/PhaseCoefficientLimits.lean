import OAI.Analysis.KadisonKastler.AmplificationPartition
import OAI.Analysis.KadisonKastler.PhaseQuotient
import OAI.Analysis.KadisonKastler.ConcreteCoefficientLimits
import OAI.Analysis.KadisonKastler.MatrixLiftBounds

namespace OAI

/-! # Coefficient limits for the actual randomized matrix partition -/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k : ℕ} [NeZero n] [NeZero k]

local instance phaseLimitSourceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance phaseLimitSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance phaseLimitOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance phaseLimitOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance phaseLimitMatrixOrder :
    PartialOrder (Algebra (matrixVonNeumann (ι := Fin n) M)) := CStarAlgebra.spectralOrder _
local instance phaseLimitMatrixStarOrder :
    StarOrderedRing (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  CStarAlgebra.spectralOrderedRing _

omit [NeZero n] [NeZero k] in
/-- The supports of both signs of the actual phase coefficients match
exactly the support projections in the clipped-column estimate. -/
theorem amplificationPhaseCoefficients_support
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (w : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (r j : ℕ) (s : Sym (Fin (n * k)) (r + 1)) :
    (let K := positivePhaseCoefficientSequence (amplificationPartition E) w (r + 1) s j
     concreteMatrixEntries (M := M) (n := n) K = concreteMatrixEntries (M := M) (n := n) K *
       supportProjection (E.map M.toStarSubalgebra.subtype) (amplificationSupport s.val)) ∧
    (let K := negativePhaseCoefficientSequence (amplificationPartition E) w (r + 1) s j
     concreteMatrixEntries (M := M) (n := n) K = concreteMatrixEntries (M := M) (n := n) K *
       supportProjection (E.map M.toStarSubalgebra.subtype) (amplificationSupport s.val)) := by
  have hmul (a b : Fin (n * k)) :
      amplificationPartition E a * amplificationPartition E b =
        if a = b then amplificationPartition E a else 0 := by
    split_ifs with hab
    · subst b
      exact (amplificationPartition_projection E a).isIdempotentElem.eq
    · exact amplificationPartition_orthogonal E a b hab
  have hs := phaseCoefficientSequence_right_support (amplificationPartition E) w
    (fun a => (amplificationPartition_projection E a).isSelfAdjoint.star_eq) hmul r s j
  constructor
  · have hm := congrArg (concreteMatrixEntries (M := M) (n := n)) hs.1.symm
    rw [map_mul, concreteMatrixEntries_phaseSupport] at hm
    exact hm
  · have hm := congrArg (concreteMatrixEntries (M := M) (n := n)) hs.2.symm
    rw [map_mul, concreteMatrixEntries_phaseSupport] at hm
    exact hm

omit [NeZero n] [NeZero k] in
/-- The actual two coefficient columns remain contractions in the original
representation. -/
theorem amplificationPhaseCoefficients_contract
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (w : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (r j : ℕ) (z : Generator.FiniteHilbert (Fin n) H) :
    ‖WithLp.toLp 2 (fun s : Sym (Fin (n * k)) (r + 1) =>
      (positivePhaseCoefficientSequence (amplificationPartition E)
        (w : BoundedSequence _) (r + 1) s j).val z)‖ ≤ ‖z‖ ∧
    ‖WithLp.toLp 2 (fun s : Sym (Fin (n * k)) (r + 1) =>
      (negativePhaseCoefficientSequence (amplificationPartition E)
        (w : BoundedSequence _) (r + 1) s j).val z)‖ ≤ ‖z‖ := by
  have hmul (a b : Fin (n * k)) :
      amplificationPartition E a * amplificationPartition E b =
        if a = b then amplificationPartition E a else 0 := by
    split_ifs with hab
    · subst b
      exact (amplificationPartition_projection E a).isIdempotentElem.eq
    · exact amplificationPartition_orthogonal E a b hab
  have hc := phaseCoefficientSequence_column_norm
    (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype
    (amplificationPartition E) w
    (fun a => (amplificationPartition_projection E a).isSelfAdjoint.star_eq)
    hmul (amplificationPartition_total E) r j z
  exact ⟨hc.1.le, hc.2.le⟩

variable {B : Type v} [CStarAlgebra B] {σ : FaithfulTracialState B} {ω : Ultrafilter ℕ}
variable {τ : FaithfulTracialState (Algebra (matrixVonNeumann (ι := Fin n) M))}
variable (R : TraceQuotientMap τ σ ω)
variable (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
variable (w : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))

/-- The free-word bound specialized to the concrete matrix partition. -/
theorem amplificationPhaseCoefficients_quotient_bounds
    (hFock : PublishedDiagonalFockRepresentation.{v})
    (htrace : ∀ a, τ.toLinearMap (amplificationPartition E a) = ((n * k : ℕ) : ℂ)⁻¹)
    (hfree : FreeHaarMoments σ R.constant.range
      (Unitary.map (StarMonoidHom.ofClass R.quotient) w))
    (r : ℕ) (hword : freeWordThreshold (r + 1) ≤ n * k) :
    (∀ s : Sym (Fin (n * k)) (r + 1),
      ‖R.quotient (positivePhaseCoefficientSequence (amplificationPartition E)
        (w : BoundedSequence _) (r + 1) s)‖ ≤
          projectionWordWeight (freeWordC (r + 1)) s) ∧
    (∀ s : Sym (Fin (n * k)) (r + 1),
      ‖R.quotient (negativePhaseCoefficientSequence (amplificationPartition E)
        (w : BoundedSequence _) (r + 1) s)‖ ≤
          projectionWordWeight (freeWordC (r + 1)) s) := by
  exact phaseCoefficientSequence_quotient_norm_bounds hFock R
    (amplificationPartition E) w
    (amplificationPartition_projection E) (amplificationPartition_orthogonal E)
    (amplificationPartition_total E) htrace
    hfree (by omega) hword

variable (hτ : FiniteVectorTrace τ)
variable (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
variable (r : ℕ) (hrk : r + 1 ≤ k)
variable (hthrough : ∀ a : Fin (n * k),
  (∑ s : ThroughLabel a (r + 1), projectionWordWeight (freeWordC (r + 1)) s.val ^ 2) ≤ 64)
variable (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
variable (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)

include hτ hCyclic hrk hthrough hδ hb in
/-- Specialization of the fixed-vector clipping limit to negative coefficients. -/
theorem negative_amplification_coefficient_limit_of_bounds
    (hbound : ∀ s : Sym (Fin (n * k)) (r + 1),
      ‖R.quotient (negativePhaseCoefficientSequence (amplificationPartition E)
        (w : BoundedSequence _) (r + 1) s)‖ ≤
          projectionWordWeight (freeWordC (r + 1)) s)
    (z : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖WithLp.toLp 2 (fun s : Sym (Fin (n * k)) (r + 1) =>
        (T * (negativePhaseCoefficientSequence (amplificationPartition E)
          (w : BoundedSequence _) (r + 1) s j).val -
        (negativePhaseCoefficientSequence (amplificationPartition E)
          (w : BoundedSequence _) (r + 1) s j).val * T) z)‖ ≤ 66 * δ * ‖z‖ + ε := by
  let S : Sym (Fin (n * k)) (r + 1) → Finset (Fin n × Fin k) :=
    fun a => amplificationSupport a.val
  let K : Sym (Fin (n * k)) (r + 1) →
      BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
    negativePhaseCoefficientSequence (amplificationPartition E) w.val (r + 1)
  let β : Sym (Fin (n * k)) (r + 1) → ℝ :=
    fun a => projectionWordWeight (freeWordC (r + 1)) a
  have hE : (E.map M.toStarSubalgebra.subtype).algebra ≤ M.toStarSubalgebra :=
    mappedMatrixUnits_algebra_le E
  have hS : ∀ a, (S a).card ≤ k := fun a => amplificationSupport_small a hrk
  have hKsupport : ∀ j a, concreteMatrixEntries (M := M) (n := n) (K a j) =
      concreteMatrixEntries (M := M) (n := n) (K a j) *
        supportProjection (E.map M.toStarSubalgebra.subtype) (S a) :=
    by
      intro j a
      dsimp only [K, S]
      exact (amplificationPhaseCoefficients_support (M := M) (n := n) (k := k)
        E w.val r j a).2
  have hβpos : ∀ a, 0 < β a := fun a => amplificationProjectionWordWeight_pos a
  have hKcontract : ∀ j (z : Generator.FiniteHilbert (Fin n) H),
      ‖WithLp.toLp 2 (fun a => (K a j).val z)‖ ≤ ‖z‖ :=
    fun j z => (amplificationPhaseCoefficients_contract E w r j z).2
  have hβ : ∀ p : Fin n × Fin k, (∑ a, if p ∈ S a then β a ^ 2 else 0) ≤ 64 :=
    amplificationSupport_weight_sum_le _ hthrough
  exact concrete_coefficient_drift_fixed R hτ hCyclic
    (E.map M.toStarSubalgebra.subtype) hE S hS K hKsupport β hβpos hKcontract hβ hbound h hδ hb z

include hτ hCyclic hrk hthrough hδ hb in
/-- The negative coefficients have restored drift at most `66δ` on
 every fixed vector, before phase averaging. -/
theorem negative_amplification_coefficient_limit
    (hFock : PublishedDiagonalFockRepresentation.{v})
    (htrace : ∀ a, τ.toLinearMap (amplificationPartition E a) = ((n * k : ℕ) : ℂ)⁻¹)
    (hfree : FreeHaarMoments σ R.constant.range
      (Unitary.map (StarMonoidHom.ofClass R.quotient) w))
    (hword : freeWordThreshold (r + 1) ≤ n * k)
    (z : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖WithLp.toLp 2 (fun s : Sym (Fin (n * k)) (r + 1) =>
        (T * (negativePhaseCoefficientSequence (amplificationPartition E)
          (w : BoundedSequence _) (r + 1) s j).val -
        (negativePhaseCoefficientSequence (amplificationPartition E)
          (w : BoundedSequence _) (r + 1) s j).val * T) z)‖ ≤ 66 * δ * ‖z‖ + ε := by
  exact negative_amplification_coefficient_limit_of_bounds R E w hτ hCyclic r hrk
    hthrough h hδ hb (amplificationPhaseCoefficients_quotient_bounds R E w hFock htrace hfree r hword).2 z

include hτ hCyclic hrk hthrough hδ hb in
/-- The positive coefficient column has drift `68δ` on vectors moved
by the controlled unitary lift. -/
theorem positive_amplification_coefficient_limit_of_bounds
    (hbound : ∀ s : Sym (Fin (n * k)) (r + 1),
      ‖R.quotient (positivePhaseCoefficientSequence (amplificationPartition E)
        (w : BoundedSequence _) (r + 1) s)‖ ≤
          projectionWordWeight (freeWordC (r + 1)) s)
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (hs : ∀ j, let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
        ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ)
    (y : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖WithLp.toLp 2 (fun a : Sym (Fin (n * k)) (r + 1) =>
        (T * (positivePhaseCoefficientSequence (amplificationPartition E)
          (w : BoundedSequence _) (r + 1) a j).val -
        (positivePhaseCoefficientSequence (amplificationPartition E)
          (w : BoundedSequence _) (r + 1) a j).val * T)
            (((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val y))‖ ≤
          68 * δ * ‖y‖ + ε := by
  let S : Sym (Fin (n * k)) (r + 1) → Finset (Fin n × Fin k) :=
    fun a => amplificationSupport a.val
  let K : Sym (Fin (n * k)) (r + 1) →
      BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
    positivePhaseCoefficientSequence (amplificationPartition E) w.val (r + 1)
  let β : Sym (Fin (n * k)) (r + 1) → ℝ :=
    fun a => projectionWordWeight (freeWordC (r + 1)) a
  have hE : (E.map M.toStarSubalgebra.subtype).algebra ≤ M.toStarSubalgebra :=
    mappedMatrixUnits_algebra_le E
  have hS : ∀ a, (S a).card ≤ k := fun a => amplificationSupport_small a hrk
  have hKsupport : ∀ j a, concreteMatrixEntries (M := M) (n := n) (K a j) =
      concreteMatrixEntries (M := M) (n := n) (K a j) *
        supportProjection (E.map M.toStarSubalgebra.subtype) (S a) :=
    by
      intro j a
      dsimp only [K, S]
      exact (amplificationPhaseCoefficients_support (M := M) (n := n) (k := k)
        E w.val r j a).1
  have hβpos : ∀ a, 0 < β a := fun a => amplificationProjectionWordWeight_pos a
  have hKcontract : ∀ j (z : Generator.FiniteHilbert (Fin n) H),
      ‖WithLp.toLp 2 (fun a => (K a j).val z)‖ ≤ ‖z‖ :=
    fun j z => (amplificationPhaseCoefficients_contract E w r j z).1
  have hβ : ∀ p : Fin n × Fin k, (∑ a, if p ∈ S a then β a ^ 2 else 0) ≤ 64 :=
    amplificationSupport_weight_sum_le _ hthrough
  exact concrete_coefficient_drift_moving R hτ hCyclic
    (E.map M.toStarSubalgebra.subtype) hE S hS K hKsupport β hβpos hKcontract hβ hbound h hδ hb s hs y

end

end KadisonKastler

end OAI
