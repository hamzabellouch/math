import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientIncrementBounds
import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientSmooth

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma coefficient_firstJet_dist_le
    (c d : BaseModel → CoefficientPoint BaseModel)
    (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d) (x : BaseModel)
    {eta : ℝ} (h0 : ‖d x-c x‖ ≤ eta)
    (h1 : ‖fderiv ℝ (fun y ↦ d y-c y) x‖ ≤ eta) :
    dist ((d x,fderiv ℝ d x) : CoefficientFirstJet BaseModel)
      (c x,fderiv ℝ c x) ≤ eta := by
  rw [Prod.dist_eq]
  apply max_le
  · simpa only [dist_eq_norm] using h0
  · rw [fderiv_fun_sub (hd.differentiable (by simp) x) (hc.differentiable (by simp) x)] at h1
    simpa only [dist_eq_norm] using h1

lemma coefficient_compact_strict_margin
    (c : BaseModel → CoefficientPoint BaseModel) (hc : ContDiff ℝ ∞ c)
    {r delta : ℝ} (hr : 0 ≤ r)
    (hclose : ∀ z ∈ closedBall (0 : BaseModel) r,
      dist ((c z,fderiv ℝ c z) : CoefficientFirstJet BaseModel) (roundCoefficientJet z) < delta) :
    ∃ eta > 0, ∀ z ∈ closedBall (0 : BaseModel) r,
      dist ((c z,fderiv ℝ c z) : CoefficientFirstJet BaseModel) (roundCoefficientJet z)+eta < delta := by
  let f : BaseModel → ℝ := fun z ↦
    dist ((c z,fderiv ℝ c z) : CoefficientFirstJet BaseModel) (roundCoefficientJet z)
  have hf : Continuous f :=
    (hc.continuous.prodMk (hc.continuous_fderiv (by simp))).dist roundCoefficientJet_continuous
  obtain ⟨z,hz,hmax⟩ := (isCompact_closedBall (0 : BaseModel) r).exists_isMaxOn
    ⟨0,mem_closedBall_self hr⟩ hf.continuousOn
  refine ⟨(delta-f z)/2,by have := hclose z hz; change f z < delta at this; linarith,?_⟩
  intro y hy
  have hle : f y ≤ f z := hmax hy
  have hlt := hclose z hz
  change f z < delta at hlt
  change f y+(delta-f z)/2 < delta
  linarith

theorem intrinsic_coefficient_neighborhood_preserved
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrho : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    {r delta : ℝ} (hr : 0 ≤ r)
    (hclose : ∀ z ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient A rho seedPoint z,
        fderiv ℝ (intrinsicChartCoefficient A rho seedPoint) z) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet z) < delta) :
    ∃ eps > 0, ∀ a b : Base → ℝ,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      (∀ x i, i ≤ 1 → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i j k, i ≤ 1 → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv y) j k) x‖ ≤ eps) →
      ∀ z ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
          (fun p ↦ rho p+b p) seedPoint z,
          fderiv ℝ (intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
            (fun p ↦ rho p+b p) seedPoint) z) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet z) < delta := by
  let c := intrinsicChartCoefficient A rho seedPoint
  have hc : ContDiff ℝ ∞ c := contDiff_iff_contDiffAt.mpr (fun z ↦
    intrinsicChartCoefficient_smoothAt A hA hs hp rho hrho seedPoint
      (by rw [centeredSphereChart_target]; trivial))
  obtain ⟨eta,heta,hmargin⟩ := coefficient_compact_strict_margin c hc hr hclose
  obtain ⟨C,hC,hbound⟩ := intrinsic_coefficient_increment_derivative_bound 1
  refine ⟨eta/(2*C),by positivity,?_⟩
  intro a b ha hb hbb hab z hz
  let d := intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
    (fun p ↦ rho p+b p) seedPoint
  have hdifference : ContDiff ℝ ∞ (fun y ↦ d y-c y) :=
    intrinsic_seed_increment_smooth A rho a b ha hb
  have hd : ContDiff ℝ ∞ d := by
    have h := hc.add hdifference
    simpa only [← add_sub_assoc,add_sub_cancel_left] using h
  have hinc := hbound A rho a b ha hb (eta/(2*C)) (by positivity) hbb hab
  have h0 : ‖d z-c z‖ ≤ C*(eta/(2*C)) := by
    simpa only [norm_iteratedFDeriv_zero] using hinc z 0 (by omega)
  have h1 : ‖fderiv ℝ (fun y ↦ d y-c y) z‖ ≤ C*(eta/(2*C)) := by
    simpa only [norm_iteratedFDeriv_one] using hinc z 1 (by omega)
  have hj := coefficient_firstJet_dist_le c d hc hd z h0 h1
  have he : C*(eta/(2*C)) = eta/2 := by field_simp [hC.ne']
  rw [he] at hj
  exact (dist_triangle _ ((c z,fderiv ℝ c z) : CoefficientFirstJet BaseModel) _).trans_lt
    (by have hm := hmargin z hz; linarith)

end
end Yau.Target

end OAI
