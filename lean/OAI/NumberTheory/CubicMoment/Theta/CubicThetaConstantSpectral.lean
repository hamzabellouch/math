import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteSpectral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSpatialRegularity

namespace OAI

/-! The actual constant Fourier coefficient is a linear combination of
the two height solutions with the same hyperbolic eigenvalue. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaHeightCombination_eigenvalue (s C : ℂ) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (fun _ _ t => (t:ℂ)^s+C*(t:ℂ)^(2-s)) x y v=
      s*(s-2)*((v:ℂ)^s+C*(v:ℂ)^(2-s)) := by
  let F : Fin 2 → ℝ → ℝ → ℝ → ℂ := fun i _ _ t => if i=0 then (t:ℂ)^s else C*(t:ℂ)^(2-s)
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ∀ a b t, 0<t →
      CubicThetaCoordinateAnalytic (F i) a b t := by
    intro i _ a b t ht
    fin_cases i
    · exact ⟨analyticAt_const,analyticAt_const,cubicThetaHeightPower_analytic s ht⟩
    · exact ⟨analyticAt_const,analyticAt_const,
        analyticAt_const.mul (cubicThetaHeightPower_analytic (2-s) ht)⟩
  have h := cubicThetaHyperbolicOperator_sum Finset.univ F hF x y hv
  have h' : cubicThetaHyperbolicOperator (fun _ _ t => (t:ℂ)^s+C*(t:ℂ)^(2-s)) x y v=
      cubicThetaHyperbolicOperator (fun _ _ t => (t:ℂ)^s) x y v+
      cubicThetaHyperbolicOperator (fun _ _ t => C*(t:ℂ)^(2-s)) x y v := by
    simpa [F,Fin.sum_univ_two] using h
  rw [h',cubicThetaHyperbolicOperator_height s x y hv]
  have hC : cubicThetaHyperbolicOperator (fun _ _ t => C*(t:ℂ)^(2-s)) x y v=
      C*((2-s)*((2-s)-2)*(v:ℂ)^(2-s)) := by
    calc
      _ = C*cubicThetaHyperbolicOperator
          (fun (_ _ t : ℝ) => (t:ℂ)^(2-s)) (x+0) (y+0) v :=
        cubicThetaHyperbolicOperator_translate (fun (_ _ t : ℝ) => (t:ℂ)^(2-s)) C 0 0 x y v
      _ = _ := by rw [cubicThetaHyperbolicOperator_height (2-s) _ _ hv]

  rw [hC]
  ring

lemma cubicThetaEisensteinConstantMode_analytic {s : ℂ} (hs : 1<s.re)
    {v : ℝ} (hv : 0<v) : AnalyticAt ℝ (fun t => cubicThetaEisensteinConstantMode t s) v := by
  let C : ℂ := ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*cubicThetaConstantDirichlet s
  have hG : AnalyticAt ℝ (fun t : ℝ => (t:ℂ)^s+C*(t:ℂ)^(2-s)) v :=
    (cubicThetaHeightPower_analytic s hv).add
      (analyticAt_const.mul (cubicThetaHeightPower_analytic (2-s) hv))
  apply hG.congr
  filter_upwards [eventually_gt_nhds hv] with t ht
  rw [cubicThetaEisensteinConstantMode_eq ht hs]
  dsimp [C]
  ring

theorem cubicThetaEisensteinConstantMode_eigenvalue {s : ℂ} (hs : 1<s.re)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (fun _ _ t => cubicThetaEisensteinConstantMode t s) x y v=
      s*(s-2)*cubicThetaEisensteinConstantMode v s := by
  let C : ℂ := ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*cubicThetaConstantDirichlet s
  have he (t : ℝ) (ht : 0<t) : cubicThetaEisensteinConstantMode t s=(t:ℂ)^s+C*(t:ℂ)^(2-s) := by
    rw [cubicThetaEisensteinConstantMode_eq ht hs]
    dsimp [C]
    ring
  rw [cubicThetaHyperbolicOperator_congr (fun _ _ t ht => he t ht) x y hv,
    cubicThetaHeightCombination_eigenvalue s C x y hv,he v hv]

end CubicFirstMoment

end

end OAI
