import Mathlib
import OAI.Probability.SKValue.Variation.ContactOrigin
import OAI.Probability.SKValue.Coercivity.CurvatureMoment
import OAI.Probability.SKValue.Coercivity.GapBoundary
import OAI.Probability.SKValue.Coercivity.ZeroGapHump

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue

lemma IsMinimizer.contactPotential_zero {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hγ:IsMinimizer W γ) (hX:IsDiffusion W γ X) {x:ℝ} (hx:x∈Ioo (0:ℝ) 1):
    contactPotential W γ X x=0 := by
  by_contra hne
  have hxp:0<contactPotential W γ X x:=lt_of_le_of_ne
    (hγ.contactPotential_nonneg hX ⟨hx.1.le,hx.2.le⟩) (Ne.symm hne)
  obtain ⟨a,b,ha,hax,hxb,hb,haG,hGb,hpos⟩:=positive_gap_endpoints
    hX.contactPotential_continuous (fun t ht ↦ hγ.contactPotential_nonneg hX ht)
    (by simp only [contactPotential,intervalIntegral.integral_same]) hx hxp
  have hab:a<b:=hax.trans hxb
  have ha1:a<1:=hax.trans hx.2
  have hb0:0<b:=hx.1.trans hxb
  let c:=γ.coeff x
  have he:∀t∈Ioo a b,γ.coeff t=c := fun t ht ↦
    hγ.coeff_constant_of_contactPositive hX ha hb hpos t ht x ⟨hax,hxb⟩
  let f:=fun t ↦ gradientMoment W γ X t-t
  have hf0:f a=0 := by
    rcases haG with ha0|haG
    · simp only [f,ha0,hX.moment_origin,sub_self]
    · by_cases ha0:a=0
      · simp only [f,ha0,hX.moment_origin,sub_self]
      · exact sub_eq_zero.mpr (hγ.moment_eq_at_contact hX ⟨lt_of_le_of_ne ha (Ne.symm ha0),ha1⟩ haG)
  have hGc:ContinuousOn (contactPotential W γ X) (Icc a b):=
    hX.contactPotential_continuous.mono (Icc_subset_Icc ha hb)
  have hGd:∀t∈Ioo a b,HasDerivAt (contactPotential W γ X) (-f t) t := by
    intro t ht
    simpa only [f,neg_sub] using hX.contactPotential_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
  have hfc:ContinuousOn f (Ico a 1):=
    (hX.gradientMoment_continuous.sub continuousOn_id).mono (Ico_subset_Ico_left ha)
  have hend:∀s∈Ioo a b,0<f s → ∃z∈Ioo s 1,z≤b ∧ f z≤f s := by
    apply endpoint_condition hb
    · intro hb1
      exact sub_eq_zero.mpr (hγ.moment_eq_at_contact hX ⟨hb0,hb1⟩ hGb)
    · intro t ht
      have hh:gradientMoment W γ X t≤1:=(le_abs_self _).trans
        (gradientMoment_bound W γ X ⟨(ha.trans_lt ht.1).le,ht.2.le⟩)
      dsimp only [f];linarith
  by_cases hc:c=0
  · apply positive_right_hump_impossible hax hxb hGc hGd hGb hxp hf0 ?_ hend
    intro z hz hzb
    have hv:=hX.moment_convexOn_zero_closed ha hz.2
      (fun t ht ↦ (he t ⟨ht.1,ht.2.trans_le hzb⟩).trans hc)
    exact hv.sub (concaveOn_id (convex_Icc a z))
  · have hcpos:0<c:=lt_of_le_of_ne (γ.nonneg x ⟨hx.1.le,hx.2⟩) (Ne.symm hc)
    have hGa:contactPotential W γ X a=0 := by
      rcases haG with ha0|haG
      · subst a
        have h0:=γ.origin_eq_of_constant hb0 he
        exact hγ.contact_origin_of_positive hX (by simpa only [h0] using hcpos)
      · exact haG
    let f':=fun t ↦ jetMoment W γ X JetExpr.curvatureExpr t-1
    have hfd:∀t∈Ioo a b,HasDerivAt f (f' t) t := by
      intro t ht
      have hd:=hX.momentExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
        (continuousAt_of_constant_interval ht he)
      rw [momentExpr_eq_gradientMoment] at hd
      exact hd.sub (hasDerivAt_id t)
    have hcv:ConvexOn ℝ (Ioo a b) f':=
      (hX.curvature_convexOn ha hb he).sub (concaveOn_const 1 (convex_Ioo a b))
    exact positive_hump_impossible hax hxb hb hGc hGd hGa hGb hxp hfc hfd hf0 hcv hend

theorem IsMinimizer.gradient_moment_contact {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hγ:IsMinimizer W γ) (hX:IsDiffusion W γ X):
    ∀t∈Ico (0:ℝ) 1,(∫ z,(gradient W γ t (X t z))^2 ∂W.μ)=t := by
  intro t ht
  change gradientMoment W γ X t=t
  rcases ht.1.eq_or_lt with he|he
  · rw [←he];exact hX.moment_origin
  · exact hγ.moment_eq_at_contact hX ⟨he,ht.2⟩ (hγ.contactPotential_zero hX ⟨he,ht.2⟩)
end SKValue

end

end OAI
