import OAI.Analysis.Mahler.RescalingEstimates

namespace OAI

namespace MahlerRescaling
open Set Metric Filter Asymptotics
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

noncomputable def rescale (f : E → ℂ) (m : ℕ) (ε : ℝ) (z : E) : ℂ :=
  (ε^m)⁻¹ • f (ε • z)

/-- Uniform control of the entire second-order jet of a holomorphic Taylor
remainder near the unit sphere, derived from the punctured bound. -/
theorem rescaled_holomorphic_remainder_C2_bound {f : E → ℂ} {m : ℕ} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0) (hrem : f =O[𝓝[≠] 0] (fun z : E => ‖z‖^(m+1))) :
    ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      DifferentiableOn ℂ (rescale f m ε) (ball 0 4) ∧
      ∀ z ∈ closedBall (0 : E) 2,
        ‖rescale f m ε z‖ ≤ C*ε ∧
        ‖fderiv ℂ (rescale f m ε) z‖ ≤ C*ε ∧
        ‖fderiv ℂ (fderiv ℂ (rescale f m ε)) z‖ ≤ C*ε := by
  obtain ⟨C,hC,δ,hδ,hbound⟩ := rescaled_remainder_bound hf0 hrem (by norm_num : (0 : ℝ) < 4)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  refine ⟨4*C,by positivity,min δ (r/4),lt_min hδ (by positivity),?_⟩
  intro ε hε hεδ
  have hεδ' := (lt_min_iff.mp hεδ).1
  have hεr := (lt_min_iff.mp hεδ).2
  have hmaps : MapsTo (fun z : E => ε • z) (ball 0 4) U := by
    intro z hz
    apply hrU
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
    have hz' : ‖z‖ < 4 := by simpa only [mem_ball,dist_zero_right] using hz
    have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hεr
    nlinarith
  have hd : DifferentiableOn ℂ (rescale f m ε) (ball 0 4) :=
    (hf.comp ((differentiable_id.const_smul ε).differentiableOn) hmaps).const_smul (ε^m)⁻¹
  have hcd := Mahler.contDiffOn_nat_of_differentiableOn_open isOpen_ball 2 hd
  have hcd' : ContDiffOn ℂ 1 (fderiv ℂ (rescale f m ε)) (ball 0 4) :=
    hcd.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdb := two_derivative_bounds hd (hcd'.differentiableOn (by norm_num))
    (fun z hz => hbound ε hε hεδ' z (by
      exact le_of_lt (by simpa only [mem_ball,dist_zero_right] using hz)))
  refine ⟨hd,?_⟩
  intro z hz
  obtain ⟨h0,h1,h2⟩ := hdb z hz
  exact ⟨h0.trans (by nlinarith),h1.trans (by nlinarith),by nlinarith⟩

/-- Quantitative uniform bounds tend to zero in all three jet norms. -/
theorem rescaled_holomorphic_remainder_uniform_C2 {f : E → ℂ} {m : ℕ} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0) (hrem : f =O[𝓝[≠] 0] (fun z : E => ‖z‖^(m+1))) :
    TendstoUniformlyOn (fun ε : ℝ => rescale f m ε) (fun _ => 0) (𝓝[>] 0) (closedBall 0 2) ∧
    TendstoUniformlyOn (fun ε : ℝ => fderiv ℂ (rescale f m ε)) (fun _ => 0)
      (𝓝[>] 0) (closedBall 0 2) ∧
    TendstoUniformlyOn (fun ε : ℝ => fderiv ℂ (fderiv ℂ (rescale f m ε))) (fun _ => 0)
      (𝓝[>] 0) (closedBall 0 2) := by
  obtain ⟨C,hC,δ,hδ,hbound⟩ := rescaled_holomorphic_remainder_C2_bound hU hzero hf hf0 hrem
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < δ := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < δ from
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds)] with ε hpos hlt
    exact ⟨hpos,hlt⟩
  have hsmall (η : ℝ) (hη : 0 < η) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C*ε < η := by
    have hlim : Tendsto (fun ε : ℝ => C*ε) (𝓝[>] 0) (𝓝 0) := by
      have ht := (show Continuous (fun ε : ℝ => C*ε) from
        continuous_const.mul continuous_id).tendsto 0
      simpa only [mul_zero] using ht.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    exact hlim.eventually (eventually_lt_nhds hη)
  constructor
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    filter_upwards [hevent,hsmall η hη] with ε hε hsmall'
    intro z hz
    simpa only [dist_zero_left] using ((hbound ε hε.1 hε.2).2 z hz).1.trans_lt hsmall'
  constructor
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    filter_upwards [hevent,hsmall η hη] with ε hε hsmall'
    intro z hz
    simpa only [dist_zero_left] using ((hbound ε hε.1 hε.2).2 z hz).2.1.trans_lt hsmall'
  · have hmetric : ∀ η > 0, ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall (0 : E) 2,
        dist (0 : E →L[ℂ] E →L[ℂ] ℂ) (fderiv ℂ (fderiv ℂ (rescale f m ε)) z) < η := by
      intro η hη
      filter_upwards [hevent,hsmall η hη] with ε hε hsmall'
      intro z hz
      have hdist : dist (0 : E →L[ℂ] E →L[ℂ] ℂ)
          (fderiv ℂ (fderiv ℂ (rescale f m ε)) z) =
            ‖fderiv ℂ (fderiv ℂ (rescale f m ε)) z‖ :=
        dist_zero_left (fderiv ℂ (fderiv ℂ (rescale f m ε)) z)
      rw [hdist]
      exact ((hbound ε hε.1 hε.2).2 z hz).2.2.trans_lt hsmall'
    exact (Metric.tendstoUniformlyOn_iff
      (F := fun ε : ℝ => fderiv ℂ (fderiv ℂ (rescale f m ε)))
      (f := fun _ : E => (0 : E →L[ℂ] E →L[ℂ] ℂ))
      (p := 𝓝[>] (0 : ℝ)) (s := closedBall (0 : E) 2)).mpr hmetric

end MahlerRescaling

end OAI
