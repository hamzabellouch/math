import OAI.Analysis.CircleDomains.Topology.CircleFormBoundary
import OAI.Analysis.CircleDomains.Sobolev.RoundAnnulusGreen
import OAI.Analysis.CircleDomains.Sobolev.LocalImageAreaForm
import OAI.Analysis.CircleDomains.Sobolev.ExteriorAnnulusEnergy

namespace OAI

/-! Green's identity on the actual source annulus computes the increase
of signed image-circle area as its squared holomorphic derivative. -/
open Set Filter Function MeasureTheory Metric Asymptotics Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exterior_annulus_area (hgreen : UnorientedFiniteCircleGreenFormula)
    {F : ℂ → ℂ} {R a b : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (ha : R < a) (hab : a < b) :
    signedCurveArea (fun t => F (unitCircleParam 0 b t)) -
      signedCurveArea (fun t => F (unitCircleParam 0 a t)) =
        ∫ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, ‖deriv F z‖^2 := by
  let O : Set ℂ := {z | R < ‖z‖}
  have hO : IsOpen O := isOpen_lt continuous_const continuous_norm
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) F O := (hF.contDiffOn hO).restrict_scalars ℝ
  have hRe : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (F z).re) O :=
    Complex.reCLM.contDiff.contDiffOn.comp hsm (mapsTo_univ _ _)
  have hIm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (F z).im) O :=
    Complex.imCLM.contDiff.contDiffOn.comp hsm (mapsTo_univ _ _)
  have hdiff (r : ℝ) (hr : R < r) (t : ℝ) : DifferentiableAt ℝ F (unitCircleParam 0 r t) := by
    have hz : unitCircleParam 0 r t ∈ O := by
      simpa only [O, mem_ofPred_eq, unitCircleParam, norm_circleMap_zero,
        abs_of_pos (hR.trans hr)] using hr
    exact ((hF _ hz).differentiableAt (hO.mem_nhds hz)).restrictScalars ℝ
  have hcurve (r : ℝ) : Differentiable ℝ (unitCircleParam 0 r) :=
    (contDiff_unitCircleParam 0 r).differentiable (by simp)
  rw [show (fun t => F (unitCircleParam 0 b t)) = F ∘ unitCircleParam 0 b from rfl,
    show (fun t => F (unitCircleParam 0 a t)) = F ∘ unitCircleParam 0 a from rfl,
    signedCurveArea_local_image (hdiff b (ha.trans hab)) (hcurve b),
    signedCurveArea_local_image (hdiff a ha) (hcurve a)]
  rw [round_annulus_green hgreen (hR.trans ha) hab O hO (by
    intro z hz
    have hza : a ≤ ‖z‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hz.2
    exact ha.trans_le hza) _ _ (hRe.mul (smooth_complex_partial_on hO hIm 1))
      (hRe.mul (smooth_complex_partial_on hO hIm Complex.I))]
  have he : ball (0 : ℂ) b \ closedBall 0 a = {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
    ext z
    simp only [Set.mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_le, mem_ofPred_eq, and_comm]
  rw [he]
  apply setIntegral_congr_fun ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet
  intro z hz
  have hzO : z ∈ O := ha.trans hz.1
  dsimp only
  rw [smooth_complex_jacobian_curl hO hRe hIm hzO]
  exact holomorphic_real_jacobian ((hF z hzO).differentiableAt (hO.mem_nhds hzO))

lemma exterior_annulus_energy_integrable {F : ℂ → ℂ} {R a b : ℝ}
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (ha : R < a) :
    IntegrableOn (fun z => ‖deriv F z‖^2) {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
  let C : Set ℂ := closedBall 0 b \ ball 0 a
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) b).diff isOpen_ball
  have hCO : C ⊆ {z : ℂ | R < ‖z‖} := by
    intro z hz
    exact ha.trans_le (by simpa only [mem_ball, dist_zero_right, not_lt] using hz.2)
  have hc : IntegrableOn (fun z => ‖deriv F z‖^2) C volume := (((hF.deriv (isOpen_lt continuous_const continuous_norm)).continuousOn.norm.pow 2).mono hCO).integrableOn_compact hC
  apply hc.mono_set
  intro z hz
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hz.2.le,
    by simpa only [mem_ball, dist_zero_right, not_lt] using hz.1.le⟩

end CircleDomainRigidity

end

end OAI
