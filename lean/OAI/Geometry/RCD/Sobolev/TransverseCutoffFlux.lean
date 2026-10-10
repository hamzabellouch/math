import OAI.Geometry.RCD.Sobolev.HarmonicBarrierTest

namespace OAI

/-! # Exact zero flux for a compact transverse harmonic test -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem harmonic_transverse_cutoff_flux
    (w f η : SobolevSpace μ Q) {Ω : Set X} (hΩ : IsOpen Ω)
    (hw : IsSobolevHarmonicOn μ Q Ω w) (W S : X → ℝ) (δ c : ℝ)
    (hf : SobolevSpace.toLp μ Q f =ᵐ[μ.restrict Ω]
      fun x => max (W x+δ) 0*max (c-S x) 0)
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x|≤B) (hn : ∀ x, 0≤χ x)
    (hsΩ : tsupport χ⊆Ω) (hη : SobolevSpace.toLp μ Q η =ᵐ[μ] χ)
    (hplateau : ∀ x∈Ω, -δ<W x → S x<c → χ x=1) :
    IntegrableOn (fun x => χ x*localGamma μ Q f w x) Ω μ ∧
      (∫ x in Ω, χ x*localGamma μ Q f w x ∂μ)=0 := by
  let T := SobolevSpace.cutoffCLM μ Q hχ hs hb hn f
  have hform := localGamma_cutoffCLM μ Q f η w hχ hs hb hn hη
  have hin : localGamma μ Q T w =ᵐ[μ.restrict Ω] fun x => χ x*localGamma μ Q f w x := by
    filter_upwards [hf,ae_restrict_of_ae hform,ae_restrict_of_ae hη,
      ae_restrict_of_ae (localGamma_zero_on_level μ Q η w 1),ae_restrict_mem hΩ.measurableSet]
      with x hfx hformx hηx hz hxΩ
    change localGamma μ Q (SobolevSpace.cutoffCLM μ Q hχ hs hb hn f) w x=_
    rw [hformx,hfx]
    have hzero : (max (W x+δ) 0*max (c-S x) 0)*localGamma μ Q η w x=0 := by
      by_cases hax : -δ<W x
      · by_cases htx : S x<c
        · rw [hz (hηx.trans (hplateau x hxΩ hax htx)),mul_zero]
        · rw [max_eq_right (by linarith : c-S x≤0),mul_zero,zero_mul]
      · rw [max_eq_right (by linarith : W x+δ≤0),zero_mul,zero_mul]
    rw [hzero,add_zero]
  have hout : localGamma μ Q T w =ᵐ[μ.restrict Ωᶜ] fun _ => (0:ℝ) := by
    filter_upwards [ae_restrict_of_ae hform,ae_restrict_of_ae hη,
      ae_restrict_of_ae (localGamma_zero_on_level μ Q η w 0),
      ae_restrict_mem hΩ.measurableSet.compl] with x hx hηx hz hxΩ
    have hχ0 : χ x=0 := by
      by_contra hh
      exact hxΩ (hsΩ (subset_tsupport χ hh))
    change localGamma μ Q (SobolevSpace.cutoffCLM μ Q hχ hs hb hn f) w x=0
    rw [hx,hχ0,hz (hηx.trans hχ0),zero_mul,mul_zero,zero_add]
  have hout' : ∀ᵐ x ∂μ, x∉Ω → localGamma μ Q T w x=0 :=
    (ae_restrict_iff' hΩ.measurableSet.compl).mp hout
  constructor
  · exact (localGamma_memL1 μ Q T w).integrableOn.congr hin
  · rw [← integral_congr_ae hin,setIntegral_eq_integral_of_ae_compl_eq_zero hout',
      integral_congr_ae (localGamma_comm μ Q T w),integral_localGamma_eq_energyForm]
    exact hw T (SobolevSpace.cutoffCLM_mem_dirichlet μ Q hχ hs hb hn hsΩ f)

end RegularPointCoordinates

end

end OAI
