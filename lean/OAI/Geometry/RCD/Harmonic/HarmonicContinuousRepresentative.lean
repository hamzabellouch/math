import OAI.Geometry.RCD.Harmonic.HarmonicInteriorRepresentative
import OAI.Geometry.RCD.Sobolev.HarmonicGradientConstruction
import OAI.Geometry.RCD.Harmonic.HomogeneousAffineImprovement

namespace OAI

/-! # Continuous representatives of the actual normalized harmonic coordinates -/

open Set Metric Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_continuous_representative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : X) {r : ℝ} (hr : 0 < r) (hcurv : -1≤K*(5*r)^2)
    (f : SobolevSpace (hausdorff n X) hX.quadratic)
    (hf : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (5*r)) f)
    (hnorm : harmonicTargetNorm hX p (5*r) f≤7) :
    ∃ v : X → ℝ, Continuous v ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic f =ᵐ[(hausdorff n X).restrict (ball p (2*r))] v := by
  let μ := hausdorff n X
  let f₀ := (1/7:ℝ) • f
  have hnorm₀ : harmonicTargetNorm hX p (5*r) f₀≤1 := by
    rw [harmonicTargetNorm_smul]
    norm_num
    linarith
  obtain ⟨C,_,hrep⟩ := harmonic_interior_bounded_representative hX hn hX.harmonicMeanValueInput
    (hX.harmonicGradientInput hn p) (a:=1) (τ:=2/5) zero_le_one (by norm_num) (by norm_num)
  obtain ⟨v,hv,_,he⟩ := hrep p (5*r) (by positivity) hcurv f₀ (hf.smul μ hX.quadratic (1/7)) hnorm₀
  have hrad : (2/5:ℝ)*(5*r)=2*r := by ring
  rw [hrad] at he
  refine ⟨fun x => 7*v x,continuous_const.mul hv.continuous,?_⟩
  have hcoe : SobolevSpace.toLp μ hX.quadratic f₀ =ᵐ[μ]
      fun x => (1/7:ℝ)*SobolevSpace.toLp μ hX.quadratic f x := by
    dsimp only [f₀]
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [he,ae_restrict_of_ae hcoe] with x hx hc
  rw [hx] at hc
  linarith

end RegularPointCoordinates

end

end OAI
