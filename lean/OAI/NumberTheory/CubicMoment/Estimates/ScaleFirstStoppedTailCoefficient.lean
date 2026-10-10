import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedGeometry
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedRoughness

namespace OAI

/-! Exact removal of zero distinguished coefficients before the height-tail
estimate. This proves roughness of the actual remaining support and keeps
the original stopped coefficient unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedStoppedRoughSupport (i : ℕ) (ξ X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    Finset Eisenstein :=
  (centralPrimaryFactors X).filter (fun r => distinguishedScaleCoefficient i ξ X d r ≠ 0)

lemma distinguishedScaleCoefficient_as_weights (i : ℕ) (ξ X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    distinguishedScaleCoefficient i ξ X d =
      distinguishedTupleCoefficient
        (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
        (fun a p => distinguishedStoppingWeights d a (norm p))
        primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) := by
  have he : (fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(d a).val)) =
      (fun a p => distinguishedStoppingWeights d a (norm p)) := by
    funext a p
    exact (distinguishedStoppingWeights_at d a p).symm
  unfold distinguishedScaleCoefficient
  rw [he]

lemma distinguishedScaleCoefficient_norm_le (i : ℕ) (ξ X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (r : Eisenstein) :
    ‖distinguishedScaleCoefficient i ξ X d r‖ ≤
      ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) := by
  rw [distinguishedScaleCoefficient_as_weights]
  obtain ⟨V,_hV,hw⟩ := distinguishedStoppingWeights_uniform
  simpa only [Fintype.card_fin] using distinguishedTupleCoefficient_norm
    (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun _ _ hp => (mem_primeCutoff.mp hp).1)
    (fun a p => distinguishedStoppingWeights d a (norm p))
    (fun a p _ => (hw i _ d).1 a (norm p))
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (X^ξ) (X^(2/5:ℝ)) r

lemma distinguishedStoppedRoughSupport_spec (i : ℕ) {ξ X : ℝ}
    (hX : 1 ≤ X) (hξz : ξ ≤ 2/5)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    {r : Eisenstein} (hr : r ∈ distinguishedStoppedRoughSupport i ξ X d) :
    primary r ∧ ∀ p ∈ primaryPrimeFactors r, X^ξ ≤ norm p := by
  obtain ⟨hr,hv⟩ := Finset.mem_filter.mp hr
  have hprimary := (mem_primaryElementBall.mp hr).1
  refine ⟨hprimary,?_⟩
  intro p hp
  have hpr := primaryPrimeFactor_spec hprimary hp
  rw [distinguishedScaleCoefficient_as_weights] at hv
  exact (distinguishedTupleCoefficient_prime_support
    (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun _ _ hp => (mem_primeCutoff.mp hp).1)
    (fun a p => distinguishedStoppingWeights d a (norm p))
    (fun _ _ hx1 => primeDetectorCutoff_one hx1)
    (fun _ hx => primeDetectorCutoff_zero hx)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) ξ)
    (Real.rpow_le_rpow_of_exponent_le hX hξz) hv hpr.1 hpr.2).1.le

lemma distinguishedStoppedBeta_rough_support (i : ℕ) (ρ ξ X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) :
    distinguishedStoppedBeta i ρ ξ X h early d q =
      stoppedBeta (distinguishedStoppedRoughSupport i ξ X d) (centralPrimaryFactors X)
        (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X))
          q.1 q.2.1 h (if early then X^(9/25:ℝ) else X^(38/100:ℝ))
          (X^(9/25:ℝ)) early) := by
  funext b
  exact (stoppedBeta_filter_nonzero _ _ _ _ _ _ b).symm

end CubicFirstMoment

end

end OAI
