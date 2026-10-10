import Mathlib
import OAI.Probability.SKValue.Variation.OrderVariations
import OAI.Probability.SKValue.Equations.PolynomialMoment
import OAI.Probability.SKValue.Processes.CurvatureNonneg

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma IsDiffusion.polyJet_integrable {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ico (0:ℝ) 1) (e:JetExpr):
    Integrable (fun z ↦ polyJet (phi W γ) e t (X t z)) W.μ := by
  have hj:=(phi_evolution W γ ht).polyJet_joint e
  obtain ⟨C,hC,hb⟩:=hj.bounded
  apply Integrable.of_bound
  · exact ((hj.slice ⟨ht.1,le_rfl⟩).measurable.comp (hX.measurable ⟨ht.1,ht.2.le⟩)).aestronglyMeasurable
  · exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hb t ⟨ht.1,le_rfl⟩ (X t z))
lemma IsDiffusion.jetMoment_hasDerivAt_integral {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hc:ContinuousAt γ.coeff t) (e:JetExpr):
    HasDerivAt (jetMoment W γ X e) (∫ z,polyJet (phi W γ) e.sourceA t (X t z)+
      γ.coeff t*polyJet (phi W γ) e.sourceP t (X t z) ∂W.μ) t := by
  rw [integral_add (hX.polyJet_integrable ⟨ht.1.le,ht.2⟩ _) ((hX.polyJet_integrable ⟨ht.1.le,ht.2⟩ _).const_mul _),integral_const_mul]
  exact hX.jetMoment_hasDerivAt ht hc e
lemma IsDiffusion.momentExpr_hasDerivAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hc:ContinuousAt γ.coeff t):
    HasDerivAt (jetMoment W γ X JetExpr.momentExpr) (jetMoment W γ X JetExpr.curvatureExpr t) t := by
  have hd:=hX.jetMoment_hasDerivAt_integral ht hc JetExpr.momentExpr
  simpa only [polyJet,JetExpr.momentExpr_sourceA,JetExpr.momentExpr_sourceP,mul_zero,add_zero,jetMoment] using hd
lemma IsDiffusion.curvatureExpr_hasDerivAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t c:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hc:ContinuousAt γ.coeff t) (he:γ.coeff t=c):
    HasDerivAt (jetMoment W γ X JetExpr.curvatureExpr) (jetMoment W γ X (JetExpr.curvatureSlope c) t) t := by
  have hd:=hX.jetMoment_hasDerivAt_integral ht hc JetExpr.curvatureExpr
  convert hd using 1
  unfold jetMoment
  apply integral_congr_ae
  refine Eventually.of_forall (fun z ↦ ?_)
  simp only [polyJet,JetExpr.curvatureSlope_eval,JetExpr.curvatureExpr_sourceA,JetExpr.curvatureExpr_sourceP,he]
  ring
lemma IsDiffusion.curvatureSlope_hasDerivAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t c:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hc:ContinuousAt γ.coeff t) (he:γ.coeff t=c):
    HasDerivAt (jetMoment W γ X (JetExpr.curvatureSlope c))
      (∫ z,(iteratedDeriv 3 (deriv (phi W γ t)) (X t z))^2-
        12*γ.coeff t*iteratedDeriv 1 (deriv (phi W γ t)) (X t z)*(iteratedDeriv 2 (deriv (phi W γ t)) (X t z))^2+
        6*(γ.coeff t)^2*(iteratedDeriv 1 (deriv (phi W γ t)) (X t z))^4 ∂W.μ) t := by
  have hd:=hX.jetMoment_hasDerivAt_integral ht hc (JetExpr.curvatureSlope c)
  convert hd using 1
  apply integral_congr_ae
  refine Eventually.of_forall (fun z ↦ ?_)
  simp only [polyJet,JetExpr.curvatureSlope_sourceA,JetExpr.curvatureSlope_sourceP,he]
  ring
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma continuousAt_of_constant_interval {f:ℝ → ℝ} {a b c t:ℝ}
    (ht:t∈Ioo a b) (he:∀s∈Ioo a b,f s=c):ContinuousAt f t := by
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact he s hs
lemma IsDiffusion.jetMoment_continuousAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (e:JetExpr):
    ContinuousAt (jetMoment W γ X e) t := by
  obtain ⟨T,htT,hT⟩:=exists_between ht.2
  exact (hX.jetMoment_continuous ⟨ht.1.le.trans htT.le,hT⟩ e).continuousAt (Icc_mem_nhds ht.1 htT)
lemma momentExpr_eq_gradientMoment (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ):
    jetMoment W γ X JetExpr.momentExpr=gradientMoment W γ X := by
  funext t
  simp only [jetMoment,polyJet,JetExpr.momentExpr_eval,iteratedDeriv_zero,gradientMoment,gradient]
lemma IsDiffusion.curvature_convexOn {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {a b c:ℝ} (ha:0≤a) (hb:b≤1)
    (he:∀t∈Ioo a b,γ.coeff t=c):ConvexOn ℝ (Ioo a b) (jetMoment W γ X JetExpr.curvatureExpr) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo a b)
    (f':=jetMoment W γ X (JetExpr.curvatureSlope c))
  · intro t ht
    exact (hX.jetMoment_continuousAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩ _).continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact (hX.curvatureExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
      (continuousAt_of_constant_interval ht he) (he t ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact (hX.curvatureSlope_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
      (continuousAt_of_constant_interval ht he) (he t ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact hX.curvature_generator_nonneg ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
lemma IsDiffusion.moment_convexOn_zero {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {a b:ℝ} (ha:0≤a) (hb:b≤1)
    (he:∀t∈Ioo a b,γ.coeff t=0):ConvexOn ℝ (Ioo a b) (gradientMoment W γ X) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo a b)
    (f':=jetMoment W γ X JetExpr.curvatureExpr) (f'':=jetMoment W γ X (JetExpr.curvatureSlope 0))
  · exact hX.gradientMoment_continuous.mono (fun t ht ↦ ⟨(ha.trans_lt ht.1).le,ht.2.trans_le hb⟩)
  · intro t ht
    rw [interior_Ioo] at ht
    simpa only [momentExpr_eq_gradientMoment] using
      (hX.momentExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
        (continuousAt_of_constant_interval ht he)).hasDerivWithinAt (s:=interior (Ioo a b))
  · intro t ht
    rw [interior_Ioo] at ht
    exact (hX.curvatureExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
      (continuousAt_of_constant_interval ht he) (he t ht)).hasDerivWithinAt
  · intro t ht
    simp only [jetMoment,polyJet,JetExpr.curvatureSlope_eval,mul_zero,zero_mul,sub_zero]
    exact integral_nonneg (fun z ↦ sq_nonneg _)
lemma IsDiffusion.moment_convexOn_zero_closed {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {a b:ℝ} (ha:0≤a) (hb:b<1)
    (he:∀t∈Ioo a b,γ.coeff t=0):ConvexOn ℝ (Icc a b) (gradientMoment W γ X) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (f':=jetMoment W γ X JetExpr.curvatureExpr) (f'':=jetMoment W γ X (JetExpr.curvatureSlope 0))
  · exact hX.gradientMoment_continuous.mono (fun t ht ↦ ⟨ha.trans ht.1,ht.2.trans_lt hb⟩)
  · intro t ht
    rw [interior_Icc] at ht
    simpa only [momentExpr_eq_gradientMoment] using
      (hX.momentExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans hb⟩
        (continuousAt_of_constant_interval ht he)).hasDerivWithinAt (s:=interior (Icc a b))
  · intro t ht
    rw [interior_Icc] at ht
    exact (hX.curvatureExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans hb⟩
      (continuousAt_of_constant_interval ht he) (he t ht)).hasDerivWithinAt
  · intro t ht
    simp only [jetMoment,polyJet,JetExpr.curvatureSlope_eval,mul_zero,zero_mul,sub_zero]
    exact integral_nonneg (fun z ↦ sq_nonneg _)
end SKValue

end

end OAI
