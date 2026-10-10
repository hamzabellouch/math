import OAI.NumberTheory.CubicMoment.Decomposition.NoStopParameters
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedProductPairs
import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDetectorCutoff

namespace OAI

/-! The original distinguished subset weight itself is bounded by one.
The no-stop estimate therefore applies to the complete small-product branch
before any factor-count or prime-bin partition. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedSubsetWeight_norm_le_one {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w z : ℝ) (r : Eisenstein) :
    ‖distinguishedSubsetWeight ψ w z r‖ ≤ 1 := by
  rw [distinguishedSubsetWeight,norm_prod]
  exact Finset.prod_le_one₀ (fun p _ => _root_.norm_nonneg _)
    (fun p _ => distinguishedPrimeWeight_norm_le_one hψ w z p)

def distinguishedNoStopLow (ℓ : ℤ) (ρ ξ : ℝ) (Ct : ℕ) (H X₀ X : ℝ) : ℂ :=
  noStopCenteredValue
    ((primaryElementBall (Real.exp primeProductWeights.radius*X)).filter
      (fun r => norm r < X^(38/100:ℝ)))
    (distinguishedSubsetWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ) ρ (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius)
    ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X₀

theorem distinguishedNoStopLow_isLittleO
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6)) (Ct : ℕ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ∀ (ξ : ℝ) (H X₀ : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (fun X => distinguishedNoStopLow ℓ ρ ξ Ct (H X) (X₀ X) X)
        =o[atTop] firstMomentScale := by
  obtain ⟨ρ,hρ,hρ₂,hbound⟩ := noStop_patterson_isLittleO hV primeProductWeights
    ℓ hGamma (by norm_num : (0:ℝ) ≤ 1) Ct
  refine ⟨ρ,hρ,hρ₂,?_⟩
  intro ξ H X₀ hH
  apply hbound (fun _ => ())
    (fun X => (primaryElementBall (Real.exp primeProductWeights.radius*X)).filter
      (fun r => norm r < X^(38/100:ℝ)))
    (fun X => distinguishedSubsetWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    (fun _ => primeDetectorCutoff) (fun X => X^ξ) H X₀
  filter_upwards [hH] with X hH
  refine ⟨hH,?_,?_,fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩⟩
  · intro r hr
    exact (mem_primaryElementBall.mp (Finset.mem_filter.mp hr).1).1
  · intro r _hr
    exact distinguishedSubsetWeight_norm_le_one
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) _ _ r

end CubicFirstMoment

end

end OAI
