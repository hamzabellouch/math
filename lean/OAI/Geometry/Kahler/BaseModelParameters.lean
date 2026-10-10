import OAI.Geometry.Kahler.BaseModelSign

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma modelMean_continuous {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    Continuous (fun p : ℝ × ℝ => modelMean a p.1 p.2 R f) := by
  have hc : Continuous (fun p : ℝ × ℝ => ∫ y in Icc (0:ℝ) R, modelIntegrand a p.1 p.2 f y) :=
    continuous_parametric_integral_of_continuous (modelIntegrand_continuous hf a) isCompact_Icc
  have he : (fun p : ℝ × ℝ => modelMean a p.1 p.2 R f) =
    fun p : ℝ × ℝ => ∫ y in Icc (0:ℝ) R, modelIntegrand a p.1 p.2 f y := by
    funext p
    rw [modelMean,intervalIntegral.integral_of_le hR,integral_Icc_eq_integral_Ioc]
  rwa [he]

def modelGap (a : ℝ) (p : RadialProfiles a) : ℝ := 2*p.s*(Real.cosh (Real.log a)-1)-(Real.log a)^2

lemma modelGap_pos {a : ℝ} (p : RadialProfiles a) : 0 < modelGap a p := by
  unfold modelGap
  linarith [p.negativity]

lemma model_regularization_parameters {a : ℝ} (ha : 1 < a) (p : RadialProfiles a)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε η : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ η < 1/2 ∧
      κ*ε^2 ≤ modelGap a p/8 ∧ ∀ ρ ∈ Icc (1-η) 1,
      modelMean a ε ρ p.R p.f ≤ -(3/4)*modelGap a p := by
  let Δ := modelGap a p
  have hΔ : 0 < Δ := modelGap_pos p
  have hzero : modelMean a 0 1 p.R p.f < -(3/4)*Δ := by
    rw [modelMean_zero ha p]
    dsimp [Δ,modelGap] at *
    linarith [p.negativity]
  have hc := (modelMean_continuous p.smooth_f.continuous a p.R_pos.le).continuousAt (x := ((0,1):ℝ × ℝ))
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_lt_const hzero)
  let ε := min (δ/4) (min (1/2) (Real.sqrt (Δ/(8*κ))))
  let η := min (δ/4) (1/4)
  have he : 0 < ε := by dsimp [ε]; positivity
  have heta : 0 < η := by dsimp [η]; positivity
  have hed : ε ≤ δ/4 := min_le_left _ _
  have he1 : ε ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hes : ε ≤ Real.sqrt (Δ/(8*κ)) := (min_le_right _ _).trans (min_le_right _ _)
  have hetad : η ≤ δ/4 := min_le_left _ _
  have heta1 : η ≤ 1/4 := min_le_right _ _
  refine ⟨ε,η,he,by linarith,heta,by linarith,?_,?_⟩
  · have hsq := sq_le_sq₀ he.le (Real.sqrt_nonneg _) |>.mpr hes
    rw [Real.sq_sqrt (by positivity : 0 ≤ Δ/(8*κ))] at hsq
    have hm := (le_div_iff₀ (by positivity : 0 < 8*κ)).mp hsq
    change κ*ε^2 ≤ Δ/8
    nlinarith
  · intro ρ hρ
    have hdist : dist ((ε,ρ):ℝ × ℝ) (0,1) < δ := by
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,abs_of_pos he,
        abs_of_nonpos (by linarith [hρ.2] : ρ-1 ≤ 0)]
      apply max_lt
      · linarith
      · linarith [hρ.1]

    exact le_of_lt (hd (y := (ε,ρ)) hdist)

end PinchedHartogs.BaseConstruction

end

end OAI
