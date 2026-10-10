import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecomposition

namespace OAI

/-! Exact scale-first and two-stage stopping identities for the original
Gauss height windows. Every matrix retains its total-product envelope. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstTailScaleRow (i : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X d r*
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*scaleFirstTailKernel ℓ H U X (r*u)

lemma scaleFirstTail_arity_partition (i : ℕ) (ℓ : ℤ) (ξ H U : ℝ) {X : ℝ}
    (hX : 1 ≤ Real.exp primeProductWeights.radius*X) :
    (∑ r ∈ centralPrimaryFactors X,
      distinguishedTupleCoefficient
        (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
        (fun _ _ => 1) primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r*
      ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) r,
        (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*scaleFirstTailKernel ℓ H U X (r*u)) =
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        scaleFirstTailScaleRow i ℓ ξ H U X d := by
  simp_rw [distinguishedScaleCoefficient_partition i ξ hX,Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem scaleFirstTailRoughWindow_by_scale {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H U : ℝ),
      scaleFirstTailRoughWindow ℓ H U X =
        ∑ i ∈ Finset.range m,
          ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
            scaleFirstTailScaleRow i ℓ ξ H U X d := by
  obtain ⟨m,hm⟩ := distinguished_rows_by_arity hξ hξz
    (Real.exp_pos primeProductWeights.radius)
    (fun _ _ hx => primeDetectorCutoff_one hx)
    (fun _ hx => primeDetectorCutoff_zero hx)
  refine ⟨m,?_⟩
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with X hm hX
  intro ℓ H U
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le
      (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  rw [scaleFirstTailRoughWindow_full ℓ H U hXp,
    roughProduct_distinguished_slices (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) (fun _ hn => centralProductEnvelope_spec hn)
      primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (scaleFirstTailKernel ℓ H U X)]
  change (∑ r ∈ centralPrimaryFactors X,
    distinguishedSubsetWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r*
      ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) r,
        (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*scaleFirstTailKernel ℓ H U X (r*u)) = _
  rw [hm (centralPrimaryFactors X) (centralProductEnvelope X) (scaleFirstTailKernel ℓ H U X)
    (fun _ hr => mem_primaryElementBall.mp hr)
    (fun _ hn => (centralProductEnvelope_spec hn).2.1)]
  apply Finset.sum_congr rfl
  intro i _
  exact scaleFirstTail_arity_partition i ℓ ξ H U hF

def scaleFirstTailNoStopRow (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X d r*
    ∑ u ∈ centralPrimaryFactors X,
      ∑ m ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (r*u) with
        stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h r m ∧
        norm r*primeSurrogate (primaryPrimeFactors m)
          (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) < X^(38/100:ℝ),
        cutoffMoebius primeDetectorCutoff (X^ξ) m*scaleFirstTailKernel ℓ H U X (r*(m*u))

def scaleFirstTailStoppedRow (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
      (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
    (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*
      ∑ a ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
        ∑ b ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
          distinguishedStoppedAlpha ρ ξ X q a*distinguishedStoppedBeta i ρ ξ X h early d q b*
            (if a*b ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X (a*b) else 0)

theorem scaleFirstTailScaleRow_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (ℓ : ℤ) (H U : ℝ) (h : ℕ)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      distinguishedScaleLength d < X^(69/200:ℝ) →
      scaleFirstTailScaleRow i ℓ ξ H U X d =
        scaleFirstTailNoStopRow i ℓ ρ ξ H U X h d+
        scaleFirstTailStoppedRow i ℓ ρ ξ H U X h true d+
        scaleFirstTailStoppedRow i ℓ ρ ξ H U X h false d := by
  filter_upwards [eventually_distinguishedScale_low_initial i ξ,
    eventually_ge_atTop (1:ℝ)] with X hstart hX
  intro ρ hρ hρ₂ ℓ H U h d hd
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  have he := roughProduct_matrix_two_stage (centralProductEnvelope X) (centralPrimaryFactors X)
    hρ hρ₂ hF (fun _ hn => centralProductEnvelope_spec hn)
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (distinguishedScaleCoefficient i ξ X d) (fun r _ hr => hstart d hd r hr)
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (9/25:ℝ) ≤ 38/100))
    h primeDetectorCutoff (X^ξ) (scaleFirstTailKernel ℓ H U X)
  unfold scaleFirstTailScaleRow
  rw [he]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · unfold scaleFirstTailNoStopRow stoppingFailedPrefix
      apply Finset.sum_congr rfl
      intro r _
      congr 1
    · rfl
  · rfl

def scaleFirstTailStoppedDyad (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) : ℂ :=
  ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
    ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
      distinguishedStoppedAlpha ρ ξ X q a*distinguishedStoppedBeta i ρ ξ X h early d q b*
        (if a*b ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X (a*b) else 0)

theorem scaleFirstTailStoppedRow_dyads (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    scaleFirstTailStoppedRow i ℓ ρ ξ H U X h early d =
      ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              scaleFirstTailStoppedDyad i ℓ ρ ξ H U X h early d q j k := by
  unfold scaleFirstTailStoppedRow
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact stopped_matrix_dyadic _ _
    (fun a ha => primaryPairSupport_primary _ _
      (fun _ hn => (mem_primaryElementBall.mp hn).1)
      (fun _ hn => (mem_primaryElementBall.mp hn).1) ha)
    (fun b hb => primaryPairSupport_primary _ _
      (fun _ hn => (mem_primaryElementBall.mp hn).1)
      (fun _ hn => (mem_primaryElementBall.mp hn).1) hb)
    _ _ _ X

end CubicFirstMoment

end

end OAI
