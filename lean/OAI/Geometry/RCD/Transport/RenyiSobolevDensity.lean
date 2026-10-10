import OAI.Geometry.RCD.Metric.ExponentialDensityIntegrals

namespace OAI

/-! # A normalized Sobolev reference density for the finite-dimensional argument -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [NeZero μ]
  (hQ : QuadraticCheegerEnergy μ)

 theorem exists_renyi_sobolev_density (p : X) {V B s : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (hs : 0 < s)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R)) :
    ∃ (a c : ℝ) (ρ : SobolevSpace μ hQ), 0 < a ∧ 8*(B+1) ≤ a ∧ 0 < c ∧
      (SobolevSpace.toLp μ hQ ρ =ᵐ[μ] fun x => c*Real.exp (-a*dist p x)) ∧
      Integrable (SobolevSpace.toLp μ hQ ρ) μ ∧
      (∫ x, SobolevSpace.toLp μ hQ ρ x ∂μ)=1 ∧
      Integrable (fun x => (SobolevSpace.toLp μ hQ ρ x)^s) μ ∧
      Integrable (fun x => Real.exp ((3*a/4)*dist p x))
        (μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x))) ∧
      FiniteSecondMoment (μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x))) := by
  let a := 8*(B+1)+(B+1)/s
  have ha8 : 8*(B+1) ≤ a := by exact le_add_of_nonneg_right (div_nonneg (by linarith) hs.le)
  have ha : 0 < a := lt_of_lt_of_le (by positivity : 0 < 8*(B+1)) ha8
  have has : B < a*s := by
    have he : a*s=8*(B+1)*s+(B+1) := by dsimp [a]; field_simp
    rw [he]
    nlinarith [mul_pos (by positivity : 0 < 8*(B+1)) hs]
  have hi := integrable_exp_neg_dist_of_volume μ p hV hB (by linarith : B < a) hvol
  have hi2 := integrable_exp_neg_dist_of_volume μ p hV hB (by linarith : B < 2*a) hvol
  let c := (∫ x, Real.exp (-a*dist p x) ∂μ)⁻¹
  have hz : 0 < ∫ x, Real.exp (-a*dist p x) ∂μ := integral_exp_pos hi
  have hc : 0 < c := inv_pos.mpr hz
  obtain ⟨ρ,hρ⟩ := exponential_sobolev μ hQ p ha.le hc hi2
  have hfi : Integrable (SobolevSpace.toLp μ hQ ρ) μ := (hi.const_mul c).congr hρ.symm
  have hm : (∫ x, SobolevSpace.toLp μ hQ ρ x ∂μ)=1 := by
    rw [integral_congr_ae hρ,integral_const_mul]
    exact inv_mul_cancel₀ hz.ne'
  have hpow := exponential_density_power_integrable μ p hV hB hc.le has hvol
  have hpowρ : Integrable (fun x => (SobolevSpace.toLp μ hQ ρ x)^s) μ :=
    hpow.congr (hρ.symm.fun_comp (fun t : ℝ => t^s))
  have hmeasure : μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x))=
      μ.withDensity (fun x => ENNReal.ofReal (c*Real.exp (-a*dist p x))) :=
    withDensity_congr_ae (hρ.fun_comp ENNReal.ofReal)
  have hexp := exponential_density_moment_integrable μ p hV hB (c := c)
    (by linarith : B < a-3*a/4) hvol
  have hdist := exponential_density_second_moment μ p (a := a) hV hB hc.le (by linarith) hvol
  refine ⟨a,c,ρ,ha,ha8,hc,hρ,hfi,hm,hpowρ,?_,?_⟩
  · rwa [hmeasure]
  · rw [hmeasure]
    exact finiteSecondMoment_of_integrable_dist _ p hdist

end RegularPointCoordinates

end

end OAI
