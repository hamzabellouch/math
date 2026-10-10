import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientNeighborhood
import OAI.Geometry.NodalSets.Elliptic.SmallRoundPerturbation

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff
noncomputable section
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem small_round_perturbation_in_comparison_neighborhood
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) {r delta : ℝ} (hr : 0 ≤ r)
    (hclose : ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta) :
    ∃ eta > 0, ∀ t : ℝ, |t| < eta → ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient (fun x ↦ d.tensor x+roundTensorPerturbation (fun z ↦ t*a z) x)
        (fun x ↦ d.density x+t*b x) seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient (fun x ↦ d.tensor x+roundTensorPerturbation (fun z ↦ t*a z) x)
          (fun x ↦ d.density x+t*b x) seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta := by
  let c := intrinsicChartCoefficient d.tensor d.density seedPoint
  let f := intrinsicChartCoefficient (roundTensorPerturbation a) b seedPoint
  have hc : ContDiff ℝ ∞ c := intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd seedPoint
  have hf : ContDiff ℝ ∞ f := intrinsic_round_increment_smooth a b ha hb seedPoint
  obtain ⟨eps,heps,hmargin⟩ := coefficient_compact_strict_margin c hc hr hclose
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : BaseModel) r).exists_bound_of_continuousOn
    (hf.continuous.prodMk (hf.continuous_fderiv (by simp))).continuousOn
  let C : ℝ := max B 0+1
  have hC : 0 < C := by dsimp [C]; have := le_max_right B 0; linarith
  have hBC : B ≤ C := by dsimp [C]; have := le_max_left B 0; linarith
  refine ⟨eps/C,div_pos heps hC,?_⟩
  intro t ht y hy
  let c' : BaseModel → CoefficientPoint BaseModel := fun z ↦ c z+t • f z
  have hc' : ContDiff ℝ ∞ c' := hc.add (hf.const_smul t)
  have hid : intrinsicChartCoefficient (fun x ↦ d.tensor x+roundTensorPerturbation (fun z ↦ t*a z) x)
      (fun x ↦ d.density x+t*b x) seedPoint = c' := by
    funext z
    have h := intrinsicChartCoefficient_increment d.tensor (roundTensorPerturbation (fun z ↦ t*a z))
      d.density (fun z ↦ t*b z) seedPoint z
    rw [intrinsic_round_increment_smul] at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  rw [hid]
  have hnorm : ‖(f y,fderiv ℝ f y)‖ ≤ C := (hB y hy).trans hBC
  have h0 : ‖f y‖ ≤ C := (le_max_left _ _).trans hnorm
  have h1 : ‖fderiv ℝ f y‖ ≤ C := (le_max_right _ _).trans hnorm
  have hdiff : (fun z ↦ c' z-c z) = fun z ↦ t • f z := by funext z; dsimp [c']; abel
  have hj := coefficient_firstJet_dist_le c c' hc hc' y
    (show ‖c' y-c y‖ ≤ |t| *C by
      change ‖(fun z ↦ c' z-c z) y‖ ≤ _
      rw [hdiff,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h0 (abs_nonneg t))
    (show ‖fderiv ℝ (fun z ↦ c' z-c z) y‖ ≤ |t| *C by
      rw [hdiff,fderiv_fun_const_smul (hf.differentiable (by simp) y)]
      exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ f y)).trans
        (by simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left h1 (abs_nonneg t)))
  have htC := (lt_div_iff₀ hC).mp ht
  exact (dist_triangle _ ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) _).trans_lt
    (by have hm := hmargin y hy; linarith)

end
end Yau.Target

end OAI
