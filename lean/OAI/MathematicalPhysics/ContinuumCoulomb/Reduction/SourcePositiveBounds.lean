import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorUnaryProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialUnaryBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceNormalizationCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceEncodingSize

namespace OAI

/-! The actual source normalization and metadata programs give one fixed
polynomial coefficient exponent for the final positive-spin graph. -/

noncomputable section
namespace ContinuumCoulomb.SourceMetadataProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

attribute [local irreducible] MediatorParameters.finalWeight

abbrev finalBound (k : ℕ) (d : BinaryHeisenberg) : ℕ :=
  MediatorParameters.finalWeight
    (SourceNormalizationProgram.normalized (input k d)).1.1
    (SourceNormalizationProgram.normalized (input k d)).1.2.1
    (SourceNormalizationProgram.normalized (input k d)).1.2.2.1

noncomputable opaque normalizedEnvironmentProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode
    envCode (fun d => (SourceNormalizationProgram.normalized (input k d)).1) :=
  (Procedure.first envCode (listCode bondCode)).comp (normalizedProgram k)

noncomputable opaque finalBoundProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode
    unaryCode ((fun x : Env => MediatorParameters.finalWeight x.1 x.2.1 x.2.2.1) ∘
      (fun d => (SourceNormalizationProgram.normalized (input k d)).1)) :=
  MediatorUnaryProgram.finalWeight.comp (normalizedEnvironmentProgram k)

theorem finalBound_power (k : ℕ) :
    ∃ A : ℕ, ∀ d, finalBound k d ≤ ((binaryHeisenbergCodec.encode d).length + 2) ^ A :=
  unaryProcedure_power_bound (finalBoundProgram k)

private theorem envWeight_congr (x : Env) (r W G n : ℕ) (h : x = (r, W, G, n)) :
    MediatorParameters.finalWeight x.1 x.2.1 x.2.2.1 =
      MediatorParameters.finalWeight r W G := by
  cases h
  rfl

private theorem finalBound_of_env (k : ℕ) (d : BinaryHeisenberg) (r W G n : ℕ)
    (he : (SourceNormalizationProgram.normalized (input k d)).1 = (r, W, G, n)) :
    finalBound k d = MediatorParameters.finalWeight r W G := by
  exact envWeight_congr ((SourceNormalizationProgram.normalized (input k d)).1) r W G n he

theorem finalBound_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    finalBound k d = MediatorParameters.finalWeight
      (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length
      (roundingDenominator k d + size d ^ k + 1) (size d ^ k) := by
  have he : (SourceNormalizationProgram.normalized (input k d)).1 =
      ((SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length,
        roundingDenominator k d + size d ^ k + 1, size d ^ k, d.coordinate.length) :=
    congrArg Prod.fst (normalized_eq k d h)
  exact finalBound_of_env k d
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length
    (roundingDenominator k d + size d ^ k + 1) (size d ^ k) d.coordinate.length he

theorem retained_count_le (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      d.edges.length := by
  have hf := List.length_filter_le SourceZeroFilter.keep
    (SourceNormalizedSpectrum.rounded (d.toSource h) (roundingDenominator k d))
  simpa only [SourceNormalizedSpectrum.retained, SourceNormalizedSpectrum.rounded,
    List.length_ofFn, BinaryHeisenberg.toSource] using hf

theorem positive_graph_count_bound (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    d.coordinate.length + 18 *
        (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      19 * (binaryHeisenbergCodec.encode d).length ∧
    19 * (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      19 * (binaryHeisenbergCodec.encode d).length := by
  have hr := retained_count_le k d h
  have hc := binaryHeisenberg_count_le_length d
  constructor <;> omega

/-- One fixed exponent controls every final coefficient, even when the
original source contains zero or exponentially tiny rational coefficients. -/
theorem source_positive_weight_range (k : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (d : BinaryHeisenberg) (h : d.Valid),
      d.PolynomialPromise k → ∀ e,
      (((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A)⁻¹ ≤
        ((MediatorIteration.finalGraph
          (SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d))
          (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ∧
      ((MediatorIteration.finalGraph
          (SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d))
          (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ≤
        ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A := by
  obtain ⟨A, hA⟩ := finalBound_power k
  refine ⟨A + 1, by omega, fun d h hp e => ?_⟩
  have hG : 0 < size d ^ k := pow_pos (size_pos d) k
  have hM : 0 < roundingDenominator k d :=
    SourceNormalizedSpectrum.denominator_pos d.edges.length hG
  have hW : 0 < roundingDenominator k d + size d ^ k + 1 := by omega
  have hB := SourceNormalizedSpectrum.family_bounds (d.toSource h) hM
    (polynomialPromise_weight k d h hp)
  have hlo := MediatorIteration.finalGraph_lower _ hW hG (fun i => (hB i).2) (fun i => (hB i).1) e
  have hhi := MediatorIteration.finalGraph_upper _ hW hG (fun i => (hB i).2) (fun i => (hB i).1) e
  have hsize : 2 ≤ (binaryHeisenbergCodec.encode d).length + 2 := by omega
  have hpow : (2 : ℝ) ≤ ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ (A + 1) := by
    exact_mod_cast hsize.trans (Nat.le_self_pow (by omega : A + 1 ≠ 0) _)
  constructor
  · have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow
    norm_num only [one_div] at hi
    exact hi.trans hlo
  · apply hhi.trans
    rw [← finalBound_eq k d h]
    have hn := (hA d).trans (Nat.pow_le_pow_right (by omega : 1 ≤
      (binaryHeisenbergCodec.encode d).length + 2) (by omega : A ≤ A + 1))
    exact_mod_cast hn

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
