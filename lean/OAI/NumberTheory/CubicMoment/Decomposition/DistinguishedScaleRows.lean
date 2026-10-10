import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedScalePartition

namespace OAI

/-! Exact scale-first decomposition of the central rough product. The
threshold applies to independent distinguished-prime scales, before
expanding the rough remainder. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleRow (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X k r *
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      (roughProduct primeDetectorCutoff (X^ξ) u:ℂ) *
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)

def distinguishedLowScaleRows (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength k < X^(69/200:ℝ) then
      distinguishedScaleRow i ℓ ξ Ct H X k else 0

def distinguishedHighScaleRows (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ distinguishedScaleLength k then
      distinguishedScaleRow i ℓ ξ Ct H X k else 0

lemma distinguishedScaleRows_split (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) :
    (∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      distinguishedScaleRow i ℓ ξ Ct H X k) =
      distinguishedLowScaleRows i ℓ ξ Ct H X + distinguishedHighScaleRows i ℓ ξ Ct H X := by
  unfold distinguishedLowScaleRows distinguishedHighScaleRows
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : distinguishedScaleLength k < X^(69/200:ℝ)
  · simp only [h,not_le.mpr h,ite_true,ite_false,add_zero]
  · simp only [h,le_of_not_gt h,ite_false,ite_true,zero_add]

lemma distinguishedScaleRows_eq_arity (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ)
    (H : ℝ) {X : ℝ} (hX : 1 ≤ Real.exp primeProductWeights.radius*X) :
    (∑ r ∈ centralPrimaryFactors X,
      distinguishedTupleCoefficient
        (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
        (fun _ _ => 1) primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r *
      ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) r,
        (roughProduct primeDetectorCutoff (X^ξ) u:ℂ) *
          centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)) =
      ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        distinguishedScaleRow i ℓ ξ Ct H X k := by
  simp_rw [distinguishedScaleCoefficient_partition i ξ hX,Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem centralRoughProduct_by_distinguished_scale {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ),
      centralRoughProduct ℓ H ((1+Real.log X)^Ct) X =
        ∑ i ∈ Finset.range m,
          (distinguishedLowScaleRows i ℓ ξ Ct H X +
            distinguishedHighScaleRows i ℓ ξ Ct H X) := by
  obtain ⟨m,hm⟩ := distinguished_rows_by_arity hξ hξz
    (Real.exp_pos primeProductWeights.radius)
    (fun _ _ hx => primeDetectorCutoff_one hx)
    (fun _ hx => primeDetectorCutoff_zero hx)
  refine ⟨m,?_⟩
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with X hm hX
  intro ℓ Ct H
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le
      (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  rw [centralRoughProduct_full ℓ H ((1+Real.log X)^Ct) hXp,
    roughProduct_distinguished_slices (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) (fun _ hn => centralProductEnvelope_spec hn)
      primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))]
  change (∑ r ∈ centralPrimaryFactors X,
    distinguishedSubsetWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r *
      ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) r,
        (roughProduct primeDetectorCutoff (X^ξ) u:ℂ) *
          centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)) = _
  rw [hm (centralPrimaryFactors X) (centralProductEnvelope X)
    (centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X)
    (fun _ hr => mem_primaryElementBall.mp hr)
    (fun _ hn => (centralProductEnvelope_spec hn).2.1)]
  apply Finset.sum_congr rfl
  intro i _
  rw [distinguishedScaleRows_eq_arity i ℓ ξ Ct H hF,distinguishedScaleRows_split]

lemma distinguishedScaleRow_low_restrict (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ)
      (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      distinguishedScaleLength k < X^(69/200:ℝ) →
      distinguishedScaleRow i ℓ ξ Ct H X k =
        ∑ r ∈ (centralPrimaryFactors X).filter (fun r => norm r < X^(9/25:ℝ)),
          distinguishedScaleCoefficient i ξ X k r *
          ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
            (Real.exp primeProductWeights.radius*X) r,
            (roughProduct primeDetectorCutoff (X^ξ) u:ℂ) *
              centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u) := by
  filter_upwards [eventually_distinguishedScale_low_initial i ξ] with X hX
  intro ℓ Ct H k hk
  unfold distinguishedScaleRow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hn : norm r < X^(9/25:ℝ)
  · rw [ite_eq_left hn]
  · have hz : distinguishedScaleCoefficient i ξ X k r = 0 := by
      by_contra hne
      exact hn (hX k hk r hne)
    rw [ite_eq_right hn,hz,zero_mul]

end CubicFirstMoment

end

end OAI
