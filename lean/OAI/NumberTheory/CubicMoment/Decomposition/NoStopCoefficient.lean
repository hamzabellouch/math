import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedStoppingMatrix

namespace OAI

/-! Collect the no-stop branch as an actual outer Type-I coefficient.
The surrogate test is retained in its original form. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def noStopCoefficient (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ X Z : ℝ) (b : Eisenstein) : ℂ :=
  stoppedBeta R D v ψ w (fun r m => norm r*primeSurrogate (primaryPrimeFactors m)
    (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z) b

theorem noStop_coefficient_collection (S R : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w ρ X Z : ℝ) (K : Eisenstein → ℂ) :
    (∑ r ∈ R, v r*∑ u ∈ primaryElementBall X,
      ∑ m ∈ primaryProductSlice S X (r*u) with
        norm r*primeSurrogate (primaryPrimeFactors m)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w m*K (r*(m*u))) =
    ∑ b ∈ primaryPairSupport R (primaryElementBall X),
      noStopCoefficient R (primaryElementBall X) v ψ w ρ X Z b *
        ∑ u ∈ primaryElementBall X, if b*u ∈ S then K (b*u) else 0 := by
  unfold noStopCoefficient stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [primaryProductSlice,Finset.sum_filter,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro m _hm
  have he : (r*u)*m = (r*m)*u := by ring
  simp only [he]
  split_ifs <;> ring_nf

theorem noStop_coefficient_divisor_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w ρ X Z : ℝ)
    (v : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) {b : Eisenstein} (hb : primary b) :
    ‖noStopCoefficient R D v ψ w ρ X Z b‖ ≤
      M*((metaplecticPrimaryDivisors b).card:ℝ) := by
  have hsub : R.filter (fun r => r ∣ b) ⊆ metaplecticPrimaryDivisors b := by
    intro r hr
    obtain ⟨hrR,hrb⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
      ⟨hR r hrR,norm_le_of_dvd (primary_ne_zero hb) hrb⟩,hrb⟩
  apply (stoppedBeta_divisor_bound R D hR hψ w _ v hM hv b).trans
  calc
    _ ≤ ((metaplecticPrimaryDivisors b).card:ℝ)*M :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) hM
    _ = _ := mul_comm _ _

end CubicFirstMoment

end

end OAI
