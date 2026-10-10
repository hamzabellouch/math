import Mathlib
import OAI.Geometry.PrescribedPotential.CoreBounds

namespace OAI

/-! Sobolev Interpolation. -/

noncomputable section
open Set Filter Topology MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rpow_epsilon_bound (r s t : ℝ) (hst : s < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      x^(s/2) ≤ ε*x^(t/2)+C*x^(r/2) := by
  have htend : Tendsto (fun x : ℝ => x^((s-t)/2)) atTop (nhds 0) := by
    convert tendsto_rpow_neg_atTop (show 0 < (t-s)/2 by linarith) using 1
    funext x
    congr 1
    ring
  obtain ⟨R,hR⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds hε))
  let B : ℝ := max 1 R
  have hc : ContinuousOn (fun x : ℝ => x^((s-r)/2)) (Icc 1 B) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    change x ≠ 0
    linarith [hx.1]
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max 0 C,le_max_left _ _,fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have he (a b : ℝ) : x^((a-b)/2)*x^(b/2)=x^(a/2) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  by_cases hxb : x ≤ B
  · have hb := hC x ⟨hx,hxb⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hb
    have hmul := mul_le_mul_of_nonneg_right (hb.trans (le_max_right 0 C))
      (Real.rpow_nonneg hx0.le (r/2))
    rw [he s r] at hmul
    exact hmul.trans (le_add_of_nonneg_left (mul_nonneg hε.le (Real.rpow_nonneg hx0.le _)))
  · have ht := (hR x ((le_max_right 1 R).trans (le_of_not_ge hxb)))
    have hmul := mul_le_mul_of_nonneg_right ht.le (Real.rpow_nonneg hx0.le (t/2))
    rw [he s t] at hmul
    exact hmul.trans (le_add_of_nonneg_right (mul_nonneg (le_max_left _ _) (Real.rpow_nonneg hx0.le _)))

def weightedFourier (s : ℝ) (f : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : E => ((1+‖x‖^2)^(s/2):ℝ)) (𝓕 f)

lemma weightedFourier_apply (s : ℝ) (f : 𝓢(E,ℂ)) (x : E) :
    weightedFourier s f x = (((1+‖x‖^2)^(s/2):ℝ):ℂ) * 𝓕 f x := by
  rw [weightedFourier,SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rfl

lemma fourier_schwartzCoord (s : ℝ) (f : 𝓢(E,ℂ)) :
    𝓕 (schwartzCoord s f) = SchwartzMap.toLpCLM ℂ ℂ 2 volume (weightedFourier s f) := by
  apply l2_injective
  change ((𝓕 (schwartzCoord s f) : L2 E) : 𝓢'(E,ℂ)) =
    (((weightedFourier s f).toLp 2 volume : L2 E) : 𝓢'(E,ℂ))
  rw [← Lp.fourier_toTemperedDistribution_eq,schwartzCoord_distribution,
    fourier_besselPotential_eq_smulLeftCLM_fourier_apply]
  rw [Lp.toTemperedDistribution_toLp_eq]
  rw [fourier_toTemperedDistributionCLM_eq]
  ext q
  simp only [smulLeftCLM_apply_apply,SchwartzMap.toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop :
    (fun x : E => (((1+‖x‖^2)^(s/2):ℝ):ℂ)).HasTemperateGrowth),
    weightedFourier_apply,smul_eq_mul]
  ring

lemma schwartzCoord_norm_weightedFourier (s : ℝ) (f : 𝓢(E,ℂ)) :
    ‖schwartzCoord s f‖ = ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (weightedFourier s f)‖ := by
  rw [← fourier_schwartzCoord,Lp.norm_fourier_eq]

theorem schwartz_sobolev_interpolation (r s t : ℝ) (hst : s < t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E,ℂ),
      ‖schwartzCoord s f‖ ≤ ε*‖schwartzCoord t f‖+C*‖schwartzCoord r f‖ := by
  obtain ⟨C,hC,hb⟩ := rpow_epsilon_bound r s t hst hε
  refine ⟨C,hC,fun f => ?_⟩
  let W := fun a : ℝ => SchwartzMap.toLpCLM ℂ ℂ 2 volume (weightedFourier a f)
  have hn : ‖W s‖ ≤ ‖(ε:ℂ) • W t+(C:ℂ) • W r‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(weightedFourier s f).coeFn_toLp (p:=2) (μ:=volume),
      (weightedFourier t f).coeFn_toLp (p:=2) (μ:=volume),
      (weightedFourier r f).coeFn_toLp (p:=2) (μ:=volume),
      Lp.coeFn_add ((ε:ℂ) • W t) ((C:ℂ) • W r),
      Lp.coeFn_smul (ε:ℂ) (W t), Lp.coeFn_smul (C:ℂ) (W r)] with x hs ht hr hadd hsm hsm'
    change ‖W s x‖ ≤ _
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hsm,hsm']
    change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (weightedFourier s f) x‖ ≤
      ‖(ε:ℂ) * SchwartzMap.toLpCLM ℂ ℂ 2 volume (weightedFourier t f) x+
        (C:ℂ)*SchwartzMap.toLpCLM ℂ ℂ 2 volume (weightedFourier r f) x‖
    simp only [SchwartzMap.toLpCLM_apply]
    rw [hs,ht,hr]
    simp only [weightedFourier_apply]
    simp only [← mul_assoc]
    rw [← add_mul,← Complex.ofReal_mul,← Complex.ofReal_mul,← Complex.ofReal_add]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hx : 0 ≤ 1+‖x‖^2 := by positivity
    rw [abs_of_nonneg (Real.rpow_nonneg hx _),abs_of_nonneg (add_nonneg
      (mul_nonneg hε.le (Real.rpow_nonneg hx _)) (mul_nonneg hC (Real.rpow_nonneg hx _)))]
    exact mul_le_mul_of_nonneg_right (hb _ (by nlinarith [sq_nonneg ‖x‖])) (norm_nonneg _)
  have hn' := hn.trans (norm_add_le _ _)
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg hC] at hn'
  simpa only [W,← schwartzCoord_norm_weightedFourier] using hn'

end SobolevChart

end

end OAI
