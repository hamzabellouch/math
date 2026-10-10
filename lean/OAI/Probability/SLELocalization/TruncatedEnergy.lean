import Mathlib
import OAI.Probability.SLELocalization.CommonClocks

namespace OAI


/-! Conformal localization and Rectangle Energy estimates. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma radialTruncation_fderiv_le {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r)
    {F : ℂ → ℂ} {z q : ℂ} (hd : DifferentiableAt ℂ F z) :
    ‖fderiv ℝ (radialTruncation H q r ∘ F) z‖ ≤ ‖deriv F z‖/r := by
  have hb := radialTruncation_fderiv_bound hH hr (q := q) hd
  have hs : ‖fderiv ℝ (radialTruncation H q r ∘ F) z‖^2 ≤ (‖deriv F z‖/r)^2 := by
    by_cases hh : r < ‖F z-q‖ ∧ ‖F z-q‖ < Real.exp H*r
    · rw [ite_eq_left hh] at hb
      refine hb.trans ?_
      rw [div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hr)
        (pow_le_pow_left₀ hr.le hh.1.le 2)
    · rw [ite_eq_right hh] at hb
      exact hb.trans (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) hr.le)).1 hs

lemma truncated_gradient_comp_integrable
    {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {K : Set α} (hK : IsCompact K) {c : α → ℂ} (hc : Continuous c)
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hmap : MapsTo c K U) {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) :
    IntegrableOn (fun x => ‖fderiv ℝ (radialTruncation H q r ∘ F) (c x)‖^2) K μ := by
  have hcont : ContinuousOn (fun x => deriv F (c x)) K :=
    (hF.deriv hU).continuousOn.comp hc.continuousOn hmap
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hcont
  have hm : AEStronglyMeasurable
      (fun x => ‖fderiv ℝ (radialTruncation H q r ∘ F) (c x)‖^2) (μ.restrict K) :=
    (((measurable_fderiv ℝ _).comp hc.measurable).norm.pow_const 2).aestronglyMeasurable
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  apply (integrable_const ((M/r)^2)).mono' hm
  filter_upwards [ae_restrict_mem₀ hK.nullMeasurableSet] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := (radialTruncation_fderiv_le hH hr (q := q) (hF.differentiableAt (hU.mem_nhds (hmap hx)))).trans
    (div_le_div_of_nonneg_right (hM x hx) hr.le)
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

end SLEExactGauge.RectangleEnergy

end

/-! Conformal localization and Rectangle Energy estimates. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma truncated_line_oscillation {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {z e : ℂ} (he : ‖e‖ = 1) {a b x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hmap : MapsTo (fun s : ℝ => z+s • e) (Icc a b) U)
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) :
    (radialTruncation H q r (F (z+y • e))-
      radialTruncation H q r (F (z+x • e)))^2 ≤
      (b-a)*(∫ s in a..b, ‖fderiv ℝ (radialTruncation H q r ∘ F) (z+s • e)‖^2) := by
  let c := fun s : ℝ => z+s • e
  let u := radialTruncation H q r ∘ F
  have hab := hx.1.trans hx.2
  have hc : ContDiff ℝ 1 c := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hG : ContDiffOn ℝ 1 (F ∘ c) (Icc a b) :=
    ((hF.contDiffOn hU).restrict_scalars ℝ).comp hc.contDiffOn hmap
  obtain ⟨K,hK⟩ := hG.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hLip := (radialTruncation_lipschitz hr H q).comp_lipschitzOnWith hK
  have hD := lipschitzOn_deriv_memLp hLip
  have ht := acl_oscillation_energy
    (radialTruncation_along_C1_AC hr H q (by simpa only [uIcc_of_le hab] using hG)) hD hx hy
  have hgrad := truncated_gradient_comp_integrable (μ := volume) isCompact_Icc hc.continuous hU hF hmap hH hr q
  have hderiv (s : ℝ) (hs : s ∈ Icc a b) :
      deriv (u ∘ c) s = fderiv ℝ u (c s) e := by
    apply radialTruncation_directional_deriv hH hr q (c := c) (t := s) (d := e) (hF.differentiableAt (hU.mem_nhds (hmap hs)))
    simpa only [one_smul,c,id_eq] using ((hasDerivAt_id s).smul_const e).const_add z
  have hbnd : (∫ s in a..b, (deriv (u ∘ c) s)^2) ≤
      ∫ s in a..b, ‖fderiv ℝ u (c s)‖^2 := by
    apply intervalIntegral.integral_mono_on hab
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hD.integrable_sq)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hgrad)
    intro s hs
    change (deriv (u ∘ c) s)^2 ≤ ‖fderiv ℝ u (c s)‖^2
    rw [hderiv s hs]
    have hh := (fderiv ℝ u (c s)).le_opNorm e
    rw [he,mul_one] at hh
    have hh' := pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa only [Real.norm_eq_abs,sq_abs] using hh'
  exact ht.trans (mul_le_mul_of_nonneg_left hbnd (sub_nonneg.2 hab))

theorem truncated_rectangle_two_lines {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {a b c d x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : x₁ ∈ Icc a b) (hx₂ : x₂ ∈ Icc a b)
    (hy₁ : y₁ ∈ Icc c d) (hy₂ : y₂ ∈ Icc c d)
    (hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, (x:ℂ)+(y:ℂ)*Complex.I ∈ U)
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) :
    (radialTruncation H q r (F ((x₁:ℂ)+(y₁:ℂ)*Complex.I))-
      radialTruncation H q r (F ((x₂:ℂ)+(y₂:ℂ)*Complex.I)))^2 ≤
      2*(b-a)*(∫ x in a..b, ‖fderiv ℝ (radialTruncation H q r ∘ F)
        ((x:ℂ)+(y₁:ℂ)*Complex.I)‖^2)+
      2*(d-c)*(∫ y in c..d, ‖fderiv ℝ (radialTruncation H q r ∘ F)
        ((x₂:ℂ)+(y:ℂ)*Complex.I)‖^2) := by
  have hh := truncated_line_oscillation hU hF (z := (y₁:ℂ)*Complex.I) (e := 1)
    (by simp) hx₂ hx₁ (by
      intro x hx
      simpa only [Complex.real_smul,Complex.ofReal_mul,mul_one,add_comm] using hrect x hx y₁ hy₁) hH hr q
  have hv := truncated_line_oscillation hU hF (z := (x₂:ℂ)) (e := Complex.I)
    (by simp) hy₂ hy₁ (by
      intro y hy
      simpa only [Complex.real_smul] using hrect x₂ hx₂ y hy) hH hr q
  simp only [Complex.real_smul,mul_one] at hh hv
  have hi : (∫ x in a..b, ‖fderiv ℝ (radialTruncation H q r ∘ F) ((y₁:ℂ)*Complex.I+(x:ℂ))‖^2) =
      ∫ x in a..b, ‖fderiv ℝ (radialTruncation H q r ∘ F) ((x:ℂ)+(y₁:ℂ)*Complex.I)‖^2 := by
    congr 1
    funext x
    rw [add_comm]
  rw [hi,add_comm ((y₁:ℂ)*Complex.I) (x₁:ℂ),add_comm ((y₁:ℂ)*Complex.I) (x₂:ℂ)] at hh
  nlinarith [sq_nonneg
    (radialTruncation H q r (F ((x₁:ℂ)+(y₁:ℂ)*Complex.I))+
      radialTruncation H q r (F ((x₂:ℂ)+(y₂:ℂ)*Complex.I))-
      2*radialTruncation H q r (F ((x₂:ℂ)+(y₁:ℂ)*Complex.I)))]

end SLEExactGauge.RectangleEnergy

end

/-! Conformal localization and Rectangle Energy estimates. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma radial_section_mem {z : ℂ} {a b s : ℝ} (ha : 0 < a) (hs : s ∈ Icc a b) (θ : ℝ) :
    z+s • circleMap 0 1 θ ∈ closedBall z b := by
  rw [mem_closedBall_iff_norm,add_sub_cancel_left,norm_smul,norm_circleMap_zero,abs_one,mul_one,
    Real.norm_of_nonneg (ha.trans_le hs.1).le]
  exact hs.2

lemma truncated_radial_energy {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {z : ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hball : closedBall z b ⊆ U)
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) (θ : ℝ) :
    (radialTruncation H q r (F (z+b • circleMap 0 1 θ))-
      radialTruncation H q r (F (z+a • circleMap 0 1 θ)))^2 ≤
      Real.log (b/a)*(∫ s in a..b, s*‖fderiv ℝ (radialTruncation H q r ∘ F)
        (z+s • circleMap 0 1 θ)‖^2) := by
  let c := fun s : ℝ => z+s • circleMap 0 1 θ
  let u := radialTruncation H q r ∘ F
  have hc : ContDiff ℝ 1 c := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hmap : MapsTo c (Icc a b) U := fun s hs => hball (radial_section_mem ha hs θ)
  have hG : ContDiffOn ℝ 1 (F ∘ c) (Icc a b) :=
    ((hF.contDiffOn hU).restrict_scalars ℝ).comp hc.contDiffOn hmap
  have ht := truncated_curve_weighted_energy hr ha hab q hG (H := H)
  have hgrad := truncated_gradient_comp_integrable (μ := volume) isCompact_Icc hc.continuous hU hF hmap hH hr q
  have hgradw : IntervalIntegrable
      (fun s => s*‖fderiv ℝ u (c s)‖^2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (hgrad.continuousOn_mul continuousOn_id isCompact_Icc)
  obtain ⟨K,hK⟩ := hG.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hLip := (radialTruncation_lipschitz hr H q).comp_lipschitzOnWith hK
  have hl2 := lipschitzOn_weighted_deriv_memLp ha hLip
  have hi : IntegrableOn (fun s => s*(deriv (u ∘ c) s)^2) (Ioc a b) := by
    have hh := (memLp_two_iff_integrable_sq hl2.aestronglyMeasurable).1 hl2
    apply hh.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [mul_pow,Real.sq_sqrt (ha.trans_le hs.1.le).le]
    rfl
  have hderiv (s : ℝ) (hs : s ∈ Icc a b) :
      deriv (u ∘ c) s = fderiv ℝ u (c s) (circleMap 0 1 θ) := by
    apply radialTruncation_directional_deriv hH hr q (hF.differentiableAt (hU.mem_nhds (hmap hs)))
    simpa only [one_smul,c,id_eq] using ((hasDerivAt_id s).smul_const (circleMap 0 1 θ)).const_add z
  have hbnd : (∫ s in a..b, s*(deriv (u ∘ c) s)^2) ≤
      ∫ s in a..b, s*‖fderiv ℝ u (c s)‖^2 := by
    apply intervalIntegral.integral_mono_on hab
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hi) hgradw
    intro s hs
    rw [hderiv s hs]
    apply mul_le_mul_of_nonneg_left _ (ha.trans_le hs.1).le
    have hh := (fderiv ℝ u (c s)).le_opNorm (circleMap 0 1 θ)
    rw [norm_circleMap_zero,abs_one,mul_one] at hh
    have hh' := pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa only [Real.norm_eq_abs,sq_abs] using hh'
  have hlog : 0 ≤ Real.log (b/a) := Real.log_nonneg ((one_le_div ha).2 hab)
  exact ht.trans (mul_le_mul_of_nonneg_left hbnd hlog)

end SLEExactGauge.RectangleEnergy

end

/-! Conformal localization and Rectangle Energy estimates. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

theorem truncated_circle_energy {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {z : ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hball : closedBall z b ⊆ U)
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) :
    ((∫ θ in -Real.pi..Real.pi, radialTruncation H q r (F (z+b • circleMap 0 1 θ)))-
      (∫ θ in -Real.pi..Real.pi, radialTruncation H q r (F (z+a • circleMap 0 1 θ))))^2 ≤
      2*Real.pi*Real.log (b/a)*(∫ θ in -Real.pi..Real.pi, ∫ s in a..b,
        s*‖fderiv ℝ (radialTruncation H q r ∘ F) (z+s • circleMap 0 1 θ)‖^2) := by
  let u := radialTruncation H q r ∘ F
  let D := fun θ => u (z+b • circleMap 0 1 θ)-u (z+a • circleMap 0 1 θ)
  let E := fun θ => ∫ s in a..b, s*‖fderiv ℝ u (z+s • circleMap 0 1 θ)‖^2
  have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hc (s : ℝ) (hs : s ∈ Icc a b) : Continuous (fun θ => u (z+s • circleMap 0 1 θ)) := by
    apply (radialTruncation_continuous hr H q).comp
    apply continuousOn_univ.1
    exact hF.continuousOn.comp
      (continuous_const.add ((continuous_circleMap 0 1).const_smul s)).continuousOn
      (fun θ _ => hball (radial_section_mem ha hs θ))
  have hca := hc a (left_mem_Icc.2 hab)
  have hcb := hc b (right_mem_Icc.2 hab)
  have hD : Continuous D := hcb.sub hca
  let c := fun p : ℝ × ℝ => z+p.2 • circleMap 0 1 p.1
  have hcc : Continuous c := continuous_const.add (continuous_snd.smul ((continuous_circleMap 0 1).comp continuous_fst))
  have hmap : MapsTo c (Icc (-Real.pi) Real.pi ×ˢ Icc a b) U :=
    fun p hp => hball (radial_section_mem ha hp.2 p.1)
  have hi := truncated_gradient_comp_integrable (μ := volume) (isCompact_Icc.prod isCompact_Icc)
    hcc hU hF hmap hH hr q
  have hiw : IntegrableOn (fun p : ℝ × ℝ => p.2*‖fderiv ℝ u (c p)‖^2)
      (Icc (-Real.pi) Real.pi ×ˢ Icc a b) :=
    hi.continuousOn_mul continuous_snd.continuousOn (isCompact_Icc.prod isCompact_Icc)
  have hiprod : Integrable (fun p : ℝ × ℝ => p.2*‖fderiv ℝ u (c p)‖^2)
      ((volume.restrict (Ioc (-Real.pi) Real.pi)).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.prod_restrict]
    exact hiw.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hE : IntervalIntegrable E volume (-Real.pi) Real.pi := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hp).2
    simpa only [E,intervalIntegral.integral_of_le hab,c,IntegrableOn] using hiprod.integral_prod_left
  have hcs := integral_mul_square_le (continuousOn_memLp_two_Ioc hp hD.continuousOn)
    (memLp_const (1:ℝ))
  have hid : (∫ θ in Ioc (-Real.pi) Real.pi, D θ*1) =
      (∫ θ in -Real.pi..Real.pi, u (z+b • circleMap 0 1 θ))-
      (∫ θ in -Real.pi..Real.pi, u (z+a • circleMap 0 1 θ)) := by
    simp only [mul_one,← intervalIntegral.integral_of_le hp,D]
    exact intervalIntegral.integral_sub (hcb.intervalIntegrable _ _) (hca.intervalIntegrable _ _)
  have hi1 : (∫ θ in Ioc (-Real.pi) Real.pi, (1:ℝ)^2) = 2*Real.pi := by
    rw [← intervalIntegral.integral_of_le hp]
    simp
    ring
  rw [hid,hi1,← intervalIntegral.integral_of_le hp] at hcs
  have hbound : (∫ θ in -Real.pi..Real.pi, D θ^2) ≤
      ∫ θ in -Real.pi..Real.pi, Real.log (b/a)*E θ := by
    apply intervalIntegral.integral_mono_on hp ((hD.pow 2).intervalIntegrable _ _)
      (hE.const_mul _)
    intro θ hθ
    exact truncated_radial_energy hU hF ha hab hball hH hr q θ
  rw [intervalIntegral.integral_const_mul] at hbound
  have hm := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 2*Real.pi)
  apply hcs.trans
  convert hm using 1 <;> ring

end SLEExactGauge.RectangleEnergy

end

end OAI
