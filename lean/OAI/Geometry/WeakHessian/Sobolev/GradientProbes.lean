import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatGradient
import OAI.Geometry.WeakHessian.LocalBounds.PositiveProbes

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile93
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma integrable_density_weakGradient_sq (hfin : FiniteOnBoundedSets m)
    {F : X → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) {u : X → ℝ} (hu : Integrable u m) :
    Integrable (fun x => u x*(weakGradient m F x)^2) m := by
  apply hu.mul_bdd ((weakGradient_isMinimal (localSobolev_of_lipschitz hfin hF).2).1.1.aestronglyMeasurable.pow 2)
    (c := (L:ℝ)^2)
  filter_upwards [weakGradient_le_localSlope hfin hF,weakGradient_nonneg (m := m) F] with x hx hn
  change ‖(weakGradient m F x)^2‖ ≤ (L:ℝ)^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply sq_le_sq₀ hn L.coe_nonneg |>.mpr
  exact hx.trans ((ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hF x)).trans_eq (ENNReal.coe_toReal L))

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrable_density_localSlope_sq {f u : X → ℝ} (hu : Integrable u m)
    {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable (fun x => u x*(localSlope f x).toReal^2) m := by
  apply hu.mul_bdd ((measurable_localSlope hf.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable (c := (L:ℝ)^2)
  apply ae_of_all
  intro x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
    ((ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)).trans_eq (ENNReal.coe_toReal L))

omit [MetricSpace X] [BorelSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_Lp_add_smul_mul (u v : Lp ℝ 2 m) (g : X → ℝ)
    (hu : Integrable (fun x => u x*g x) m) (hv : Integrable (fun x => v x*g x) m) (ε : ℝ) :
    (∫ x,(u+ε • v) x*g x ∂m) = (∫ x,u x*g x ∂m)+ε*(∫ x,v x*g x ∂m) := by
  calc
    _ = ∫ x,u x*g x+ε*(v x*g x) ∂m := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add u (ε • v),Lp.coeFn_smul ε v] with x h1 h2
      simp only [h1,Pi.add_apply,h2,Pi.smul_apply,smul_eq_mul]
      ring
    _ = _ := by rw [integral_add hu (hv.const_mul ε),integral_const_mul]

lemma RCD.cheegerHeat_gradient_integral_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (f F : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) (hfc : HasCompactSupport (f : X → ℝ))
    (hFl : GloballyLipschitz (F : X → ℝ)) (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f))
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B) :
    (∫ x,u x*(weakGradient m F x)^2 ∂m) ≤
      Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(localSlope f x).toReal^2 ∂m) := by
  obtain ⟨a,ha,hwi,hw,-⟩ := hrcd.1.exists_comparison_confinement hN hfull hfin o
  let w := hw.toLp (fun x => Real.exp (-(a*dist x o)))
  have hwi' : Integrable w m := hwi.congr hw.coeFn_toLp.symm
  have hgu := integrable_density_weakGradient_sq hfin hFl.choose_spec hu
  have hgw := integrable_density_weakGradient_sq hfin hFl.choose_spec hwi'
  have hsu := integrable_density_localSlope_sq (cheegerHeat_integrable hfin o h u hu ht).1 hf.choose_spec
  have hsw := integrable_density_localSlope_sq (cheegerHeat_integrable hfin o h w hwi' ht).1 hf.choose_spec
  have H (ε : ℝ) (hε : 0 < ε) :
      (∫ x,u x*(weakGradient m F x)^2 ∂m)+ε*(∫ x,w x*(weakGradient m F x)^2 ∂m) ≤
        Real.exp (-2*K*t)*((∫ x,cheegerHeat h t u x*(localSlope f x).toReal^2 ∂m)+
          ε*(∫ x,cheegerHeat h t w x*(localSlope f x).toReal^2 ∂m)) := by
    have hpos := positiveProbe_pos o hw u hun hε
    have HH := hrcd.cheegerHeat_weightedGradient_compact hN hfull hfin h o f F hf hfc hFl hf2 ht hF
      (positiveProbe o hw u ε) (positiveProbe_integrable o hw u hu hwi ε) (hpos.mono fun _ hx => hx.le)
      (densityMeasure_ac_of_pos _ hpos)
      (densityMeasure_locally_le _ (add_nonneg hB hε.le) (positiveProbe_le o ha hw u huB hε.le))
      (positiveProbe_locally_dominates o ha hw u hun hε)
    dsimp only [positiveProbe] at HH
    rw [integral_Lp_add_smul_mul u w _ hgu hgw,map_add,map_smul,
      integral_Lp_add_smul_mul _ _ _ hsu hsw] at HH
    exact HH
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have HH := le_of_tendsto_of_tendsto (tendsto_const_nhds.add (he.mul_const _))
    (tendsto_const_nhds.mul (tendsto_const_nhds.add (he.mul_const _)))
    (show ∀ᶠ ε in 𝓝[>] (0:ℝ),_ from by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact H ε hε)
  simpa only [zero_mul,add_zero] using HH
end WeakHessian

end
end InlinedFile93

end OAI
