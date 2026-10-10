import OAI.NumberTheory.CubicMoment.Estimates.UpperTailStopping
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialHeightNoStopBound

namespace OAI

/-! Propagate the constructed radial transform through the literal tail.
No radial normalization or Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_upperTailNoStopRow_finite_bound (m : ℕ) (hpnt : PrimaryPrimePNT)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ η cap : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/3) (hη : η ≤ κ/4)
    (hcap : 1 < cap) (M : ℕ) :
    ∃ ρ C E : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ᶠ X : ℝ in atTop, ∀ i < m, ∀ (ξ H U : ℝ)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
        0 < H → Real.log X ≤ U → X^(1/100:ℝ) < U → U ≤ X^(1/6+η) →
        ‖upperTailNoStopRow i 0 κ ρ ξ H U X d‖ ≤
          (1+Real.log X)*(C*X^(5/6-min (1/100) (3*κ/16))+
            E*X^(5/6:ℝ)/(Real.log X)^M) := by
  let A : ℝ := ∑ i ∈ Finset.range m, ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  obtain ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,hbound⟩ := cubicTheta_radial_height_noStop_bound
    hpnt primeProductWeights hMV hMean0 hκ hκsmall hη
    (A := A) (by dsimp [A]; positivity) hcap M
  refine ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hb hX
  intro i hi ξ H U d hH hLU hU hUhi
  have hAi : ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) ≤ A := by
    dsimp only [A]
    exact Finset.single_le_sum (f := fun j : ℕ => ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ))
      (fun j _ => by positivity) (Finset.mem_range.mpr hi)
  have he := hb () (centralPrimaryFactors X) (distinguishedScaleCoefficient i ξ X d)
    primeDetectorCutoff (X^ξ) H U X (fun _ _ => True) hLU hUhi hH hX
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (fun r _ => (distinguishedScaleCoefficient_norm i ξ X d r).trans hAi)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
  simpa only [heightNoStopThreshold,not_le.mpr hU,ite_false,upperTailNoStopRow] using he

end CubicFirstMoment

end

end OAI
