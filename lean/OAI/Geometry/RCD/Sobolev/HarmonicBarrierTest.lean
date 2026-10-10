import OAI.Geometry.RCD.Harmonic.TransversePositivePart
import OAI.Geometry.RCD.Sobolev.CutoffGamma

namespace OAI

/-! # A compact positive transverse barrier contradicts harmonicity -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.IsOpenPosMeasure] (Q : QuadraticCheegerEnergy μ)

theorem harmonic_transverse_barrier_false
    (w f η : SobolevSpace μ Q) {Ω : Set X} (hΩ : IsOpen Ω)
    (hw : IsSobolevHarmonicOn μ Q Ω w) (W S : X → ℝ)
    (hW : ContinuousOn W Ω) (hS : ContinuousOn S Ω)
    {p : X} (hp : p∈Ω) (hWp : W p=0) (hSp : S p=0)
    {δ c : ℝ} (hδ : 0<δ) (hc : 0<c)
    (hf : SobolevSpace.toLp μ Q f =ᵐ[μ.restrict Ω]
      fun x => max (W x+δ) 0*max (c-S x) 0)
    (hfw : localGamma μ Q f w =ᵐ[μ.restrict Ω]
      fun x => if -δ<W x then max (c-S x) 0 else 0)
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x|≤B) (hn : ∀ x, 0≤χ x)
    (hsΩ : tsupport χ⊆Ω) (hη : SobolevSpace.toLp μ Q η =ᵐ[μ] χ)
    (hplateau : ∀ x∈Ω, -δ<W x → S x<c → χ x=1) : False := by
  let T := SobolevSpace.cutoffCLM μ Q hχ hs hb hn f
  have hform := localGamma_cutoffCLM μ Q f η w hχ hs hb hn hη
  have hin : localGamma μ Q T w =ᵐ[μ.restrict Ω] fun x =>
      χ x*(if -δ<W x then max (c-S x) 0 else 0) := by
    filter_upwards [hf,hfw,ae_restrict_of_ae hform,ae_restrict_of_ae hη,
      ae_restrict_of_ae (localGamma_zero_on_level μ Q η w 1),ae_restrict_mem hΩ.measurableSet]
      with x hfx hfwx hformx hηx hz hxΩ
    change localGamma μ Q (SobolevSpace.cutoffCLM μ Q hχ hs hb hn f) w x=_
    rw [hformx,hfwx,hfx]
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
  have hnon : ∀ᵐ x ∂μ, 0≤localGamma μ Q T w x := by
    apply ae_of_ae_restrict_of_ae_restrict_compl Ω
    · exact hin.mono (fun x hx => hx.symm ▸ mul_nonneg (hn x) (by split_ifs <;> positivity))
    · exact hout.mono (fun _ hx => hx.symm ▸ le_refl 0)
  have hnh : {x | x∈Ω ∧ -δ<W x ∧ S x<c}∈𝓝 p := by
    have ha := (hW.continuousAt (hΩ.mem_nhds hp)).eventually (lt_mem_nhds (by rw [hWp]; linarith : -δ<W p))
    have ht := (hS.continuousAt (hΩ.mem_nhds hp)).eventually (gt_mem_nhds (by rw [hSp]; exact hc : S p<c))
    filter_upwards [hΩ.mem_nhds hp,ha,ht] with x hx hax htx
    exact ⟨hx,hax,htx⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hnh
  have hpos : ∀ᵐ x ∂μ.restrict (ball p r), 0<localGamma μ Q T w x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (fun x hx => (hrsub hx).1) hin,
      ae_restrict_mem measurableSet_ball] with x hx hxr
    obtain ⟨hxΩ,hxW,hxS⟩ := hrsub hxr
    rw [hx,hplateau x hxΩ hxW hxS,one_mul,ite_eq_left hxW]
    exact lt_of_lt_of_le (sub_pos.mpr hxS) (le_max_left _ _)
  have hzero : ∀ᵐ x ∂μ, localGamma μ Q T w x=0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae hnon (localGamma_memL1 μ Q T w)).mp
    rw [integral_congr_ae (localGamma_comm μ Q T w),integral_localGamma_eq_energyForm]
    exact hw T (SobolevSpace.cutoffCLM_mem_dirichlet μ Q hχ hs hb hn hsΩ f)
  have hfalse : ∀ᵐ x ∂μ.restrict (ball p r), False := by
    filter_upwards [hpos,ae_restrict_of_ae hzero] with x hx hz
    exact (ne_of_gt hx) hz
  have hm := ae_iff.mp hfalse
  have hball : μ (ball p r)≠0 := (isOpen_ball.measure_pos μ (nonempty_ball.mpr hr)).ne'
  exact hball (by simpa only [not_false_eq_true,ofPred_true,Measure.restrict_apply_univ] using hm)

end RegularPointCoordinates

end

end OAI
