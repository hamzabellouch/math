import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFMassRemainder
import OAI.Probability.SKBarriers.Parisi.CDFMassSegment

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFParisi_mass_quotient_bound (β : ℝ) (α γ : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hg : ∀ z, γ z∈Icc (0:ℝ) 1) (hγ1 : γ 1=1)
    {θ h : ℝ} (hθ : θ∈Ioc (0:ℝ) 1) (hh : 0<h) :
    |(scalarCDFParisi β (cdfMassSegment α γ θ)-scalarCDFParisi β α)/θ-
      (β^2/2)*∫ s in Icc (0:ℝ) 1, (γ s-α s)*(scalarCDFOverlap β α s-s)|≤
      (β^2/2)*cdfDistance γ α*scalarOverlapModulus β (θ*cdfDistance γ α) h := by
  let η := cdfMassSegmentStieltjes α γ θ ⟨hθ.1.le,hθ.2⟩
  have H := scalarCDFParisi_mass_remainder β α η ha hα1
    (cdfMassSegment_bounds ha hg ⟨hθ.1.le,hθ.2⟩) (cdfMassSegment_one hα1 hγ1 θ) hh
  change |scalarCDFParisi β (cdfMassSegment α γ θ)-scalarCDFParisi β α-
      (β^2/2)*∫ s in Icc (0:ℝ) 1, (cdfMassSegment α γ θ s-α s)*(scalarCDFOverlap β α s-s)|≤
      (β^2/2)*cdfDistance (cdfMassSegment α γ θ) α*
        scalarOverlapModulus β (cdfDistance (cdfMassSegment α γ θ) α) h at H
  rw [cdfMassSegment_distance α γ hθ.1.le,cdfMassSegment_integral] at H
  have he (a b L : ℝ) : |(a-b)/θ-L|=|a-b-θ*L|/θ := by
    have E : (a-b)/θ-L=(a-b-θ*L)/θ := by field_simp [ne_of_gt hθ.1]
    rw [E,abs_div,abs_of_pos hθ.1]
  rw [he]
  have HE : (β^2/2)*(θ*(∫ s in Icc (0:ℝ) 1, (γ s-α s)*(scalarCDFOverlap β α s-s)))=
      θ*((β^2/2)*(∫ s in Icc (0:ℝ) 1, (γ s-α s)*(scalarCDFOverlap β α s-s))) := by ring
  rw [HE] at H
  apply (div_le_div_of_nonneg_right H hθ.1.le).trans_eq
  field_simp [ne_of_gt hθ.1]

theorem scalarCDFParisi_mass_quotient_tendsto (β : ℝ) (α γ : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hg : ∀ z, γ z∈Icc (0:ℝ) 1) (hγ1 : γ 1=1) :
    Tendsto (fun θ : ℝ => (scalarCDFParisi β (cdfMassSegment α γ θ)-scalarCDFParisi β α)/θ)
      (𝓝[>] (0:ℝ)) (𝓝 ((β^2/2)*∫ s in Icc (0:ℝ) 1,
        (γ s-α s)*(scalarCDFOverlap β α s-s))) := by
  let K := (β^2/2)*cdfDistance γ α
  have hK : 0≤K := mul_nonneg (by positivity) (cdfDistance_nonneg _ _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let h := ε/(24*(K+1))
  have hh : 0<h := div_pos hε (by positivity)
  have he : K*(12*h)<ε := by
    have HE : (K+1)*(12*h)=ε/2 := by dsimp [h]; field_simp; ring
    have HH := mul_le_mul_of_nonneg_right (show K≤K+1 by linarith) (by positivity : 0≤12*h)
    rw [HE] at HH
    linarith
  have HC : Continuous (fun θ : ℝ => K*scalarOverlapModulus β (θ*cdfDistance γ α) h) :=
    continuous_const.mul ((scalarOverlapModulus_continuous β h).comp (continuous_id.mul continuous_const))
  have HT : Tendsto (fun θ : ℝ => K*scalarOverlapModulus β (θ*cdfDistance γ α) h)
      (𝓝[>] (0:ℝ)) (𝓝 (K*(12*h))) := by
    simpa only [scalarOverlapModulus,zero_mul,mul_zero,zero_div,Real.exp_zero,sub_self,add_zero,zero_add]
      using (HC.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have Hε := (tendsto_order.mp HT).2 ε he
  have H₁ : ∀ᶠ θ : ℝ in 𝓝[>] (0:ℝ), θ<1 := (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [Hε,H₁,self_mem_nhdsWithin] with θ hθε hθ1 hθ0
  rw [Real.dist_eq]
  exact (scalarCDFParisi_mass_quotient_bound β α γ ha hα1 hg hγ1 ⟨hθ0,hθ1.le⟩ hh).trans_lt hθε

theorem scalarCDFParisi_hasDerivWithinAt_mass (β : ℝ) (α γ : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hg : ∀ z, γ z∈Icc (0:ℝ) 1) (hγ1 : γ 1=1) :
    HasDerivWithinAt (fun θ : ℝ => scalarCDFParisi β (cdfMassSegment α γ θ))
      ((β^2/2)*∫ s in Icc (0:ℝ) 1, (γ s-α s)*(scalarCDFOverlap β α s-s)) (Ici (0:ℝ)) 0 := by
  have he : Ici (0:ℝ)\{0}=Ioi (0:ℝ) := by
    ext x
    simp only [Set.mem_sdiff,mem_Ici,mem_singleton_iff,mem_Ioi]
    exact ⟨fun H => lt_of_le_of_ne H.1 (Ne.symm H.2),fun H => ⟨H.le,ne_of_gt H⟩⟩
  rw [hasDerivWithinAt_iff_tendsto_slope,he]
  change Tendsto (fun θ => slope (fun θ : ℝ => scalarCDFParisi β (cdfMassSegment α γ θ)) 0 θ) _ _
  simpa only [slope_def_field,sub_zero,cdfMassSegment_zero] using
    scalarCDFParisi_mass_quotient_tendsto β α γ ha hα1 hg hγ1

end SK.Analytic

end
end

end OAI
