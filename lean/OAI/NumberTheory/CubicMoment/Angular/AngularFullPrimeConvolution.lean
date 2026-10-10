import OAI.NumberTheory.CubicMoment.Estimates.FullStructuredMeanValue
import OAI.NumberTheory.CubicMoment.Angular.AngularStructuredSupportBounds

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def fullStructuredAngularPrimeSum (R : ℝ) (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun z => IsCoprime z e),
    fullPrimeCoefficient R W X z*theta ℓ z*mellinPhase u (norm z)*cubicSymbol z (v*a*b^2)

lemma fullStructuredAngularPrimeSum_eq {R Z : ℝ} (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hhi : ∀ i x, R < x → W i x = 0) (hZ : ∀ i, R*X i ≤ 2*Z) :
    fullStructuredAngularPrimeSum ℓ R a b v e u W X = structuredAngularPrimeSum ℓ a b v e u W X Z := by
  unfold fullStructuredAngularPrimeSum fullPrimeCoefficient structuredAngularPrimeSum primeMomentCoefficient
  rw [fullPrimeSupport_eq_coordinate W X hX hhi hZ]

lemma fullStructuredAngularPrimeSum_partition_cutoff {R : ℝ} (hR : 1 ≤ R)
    (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
    (a b v e : Eisenstein) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 1 ≤ X i) (hhi : ∀ i x, R < x → W i x = 0) :
    fullStructuredAngularPrimeSum ℓ R a b v e u W X =
      structuredAngularPrimeSum ℓ a b v e u W X (((4/3:ℝ)^J/2)*(∏ i, X i)) := by
  apply fullStructuredAngularPrimeSum_eq ℓ a b v e u W X (fun i => by linarith [hX i]) hhi
  intro i
  have hi := coordinate_le_product X hX i
  have hprod : 0 ≤ ∏ i, X i := Finset.prod_nonneg (fun i _ => by linarith [hX i])
  have hk : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hRk : R ≤ R^(Fintype.card ι) := by
    exact le_self_pow₀ hR (Nat.ne_of_gt hk)
  have hRR : R ≤ (4/3:ℝ)^J := by linarith [hRk,show (0:ℝ) ≤ R^Fintype.card ι by positivity]
  nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ R by linarith),
    mul_le_mul_of_nonneg_right hRR hprod]

lemma fullStructuredAngularPrimeSum_eq_existing (R : ℝ) (h v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularPrimeSum ℓ R h 1 v e u W X =
      fullStructuredAngularSum R h v e ℓ u W X := by
  unfold fullStructuredAngularPrimeSum fullStructuredAngularSum
  apply Finset.sum_congr rfl
  intro z _
  simp only [one_pow,mul_one]
  ring

end CubicFirstMoment

end

end OAI
