import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.TailClosure

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma radial_coulomb_lintegral_inner (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {R : ℝ} (hs : ∀ s, s < R → F s=0) {x : Space} (hxR : ‖x‖ ≤ R) :
    (∫⁻ y : Space, ENNReal.ofReal ‖x-y‖⁻¹*F ‖y‖)=
      ∫⁻ y : Space, ENNReal.ofReal ‖y‖⁻¹*F ‖y‖ := by
  by_cases hx : x=0
  · simp only [hx,zero_sub,norm_neg]
  rw [radial_coulomb_lintegral F hF hx,
    radial_space_lintegral (fun s => ENNReal.ofReal s⁻¹*F s) (by fun_prop)]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs0
  dsimp only
  by_cases hR : R ≤ s
  · rw [max_eq_right (hxR.trans hR),ENNReal.ofReal_mul (sq_nonneg s),mul_assoc]
  · simp only [hs s (not_le.mp hR),mul_zero]

lemma radial_coulomb_integral_inner {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ} (hfM : ∀ y, f y ≤ M)
    (hrad : ∀ y, f y=f (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hfs : ∀ y, ‖y‖ < R → f y=0) {x : Space} (hxR : ‖x‖ ≤ R) :
    (∫ y, coulombKernel (x-y)*f y)=∫ y, coulombKernel y*f y := by
  by_cases hx : x=0
  · simp only [hx,zero_sub,coulombKernel,norm_neg]
  let F : ℝ → ℝ≥0∞ := fun s => if 0 ≤ s then ENNReal.ofReal (f (EuclideanSpace.single 0 s)) else 0
  have hmF : Measurable F := Measurable.ite measurableSet_Ici
    ((hm.comp space_axis_continuous.measurable).ennreal_ofReal) measurable_const
  have he (y : Space) : F ‖y‖=ENNReal.ofReal (f y) := by
    simp only [F,ite_eq_left (norm_nonneg y),←hrad y]
  have hs : ∀ s, s < R → F s=0 := by
    intro s hs
    by_cases hs0 : 0 ≤ s
    · have HH := hfs (EuclideanSpace.single 0 s) (by simpa [Real.norm_eq_abs,abs_of_nonneg hs0] using hs)
      simp only [F,ite_eq_left hs0,HH,ENNReal.ofReal_zero]
    · simp only [F,ite_eq_right hs0]
  have H := radial_coulomb_lintegral_inner F hmF hs hxR
  simp_rw [he] at H
  have hi := coulomb_convolution_integrable hf hm hf0 hfM (by norm_num : (0:ℝ) < 1) x
  have hi0 := coulomb_convolution_integrable hf hm hf0 hfM (by norm_num : (0:ℝ) < 1) 0
  simp only [zero_sub,coulombKernel,norm_neg] at hi0
  change Integrable (fun y => coulombKernel y*f y) at hi0
  have hp (y : Space) : 0 ≤ coulombKernel (x-y)*f y := mul_nonneg (coulombKernel_nonneg _) (hf0 _)
  have hp0 (y : Space) : 0 ≤ coulombKernel y*f y := mul_nonneg (coulombKernel_nonneg _) (hf0 _)
  have hI := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hp)
  have hI0 := ofReal_integral_eq_lintegral_ofReal hi0 (Eventually.of_forall hp0)
  simp_rw [ENNReal.ofReal_mul (coulombKernel_nonneg _)] at hI hI0
  change ENNReal.ofReal (∫ y, coulombKernel (x-y)*f y)=∫⁻ y, ENNReal.ofReal ‖x-y‖⁻¹*ENNReal.ofReal (f y) at hI
  change ENNReal.ofReal (∫ y, coulombKernel y*f y)=∫⁻ y, ENNReal.ofReal ‖y‖⁻¹*ENNReal.ofReal (f y) at hI0
  rw [←hI,←hI0] at H
  have H' := congrArg ENNReal.toReal H
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hp),ENNReal.toReal_ofReal (integral_nonneg hp0)] using H'

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def radialShell (h : ℝ) : Set Space := Metric.ball 0 (2*h) \ Metric.ball 0 h

def radialShellDensity (h : ℝ) : Space → ℝ := (radialShell h).indicator (fun _ => 1)

lemma measurableSet_radialShell (h : ℝ) : MeasurableSet (radialShell h) :=
  measurableSet_ball.diff measurableSet_ball
lemma radialShellDensity_measurable (h : ℝ) : Measurable (radialShellDensity h) :=
  measurable_const.indicator (measurableSet_radialShell h)
lemma radialShellDensity_nonneg (h : ℝ) (z : Space) : 0 ≤ radialShellDensity h z :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) z
lemma radialShellDensity_le (h : ℝ) (z : Space) : radialShellDensity h z ≤ 1 :=
  Set.indicator_le_self' (fun _ _ => zero_le_one) z
lemma radialShellDensity_integrable (h : ℝ) : Integrable (radialShellDensity h) := by
  apply (integrable_indicator_iff (measurableSet_radialShell h)).mpr
  exact integrableOn_const (C:=(1:ℝ)) (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne)

lemma radialShellDensity_mass {h : ℝ} (hh : 0 < h) :
    (∫ z, radialShellDensity h z)=(28*Real.pi/3)*h^3 := by
  unfold radialShellDensity radialShell
  rw [integral_indicator (measurableSet_ball.diff measurableSet_ball),integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one,
    measureReal_sdiff (Metric.ball_subset_ball (by linarith)) measurableSet_ball measure_ball_lt_top.ne,
    volume_real_ball_three (2*h) (by positivity),volume_real_ball_three h hh.le]
  ring

lemma radialShellDensity_radial (h : ℝ) (z : Space) :
    radialShellDensity h z=radialShellDensity h (EuclideanSpace.single 0 ‖z‖) := by
  simp only [radialShellDensity,radialShell,Set.indicator_apply,Set.mem_sdiff,Metric.mem_ball,dist_zero_right,
    PiLp.norm_single,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z)]

lemma radialShellDensity_zero_inner {h : ℝ} {z : Space} (hz : ‖z‖ < h) :
    radialShellDensity h z=0 := by
  apply Set.indicator_of_notMem
  exact fun hmem => hmem.2 (by simpa only [Metric.mem_ball,dist_zero_right] using hz)

lemma radialShell_coulomb_integrable (h : ℝ) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*radialShellDensity h y) :=
  coulomb_convolution_integrable (radialShellDensity_integrable h) (radialShellDensity_measurable h)
    (radialShellDensity_nonneg h) (radialShellDensity_le h) (by norm_num : (0:ℝ) < 1) x

def radialShellMoment (h : ℝ) : ℝ := ∫ y, coulombKernel y*radialShellDensity h y

lemma radialShellMoment_integrable (h : ℝ) :
    Integrable (fun y => coulombKernel y*radialShellDensity h y) := by
  simpa only [zero_sub,coulombKernel,norm_neg] using radialShell_coulomb_integrable h 0

lemma radialShell_coulomb_inner {h : ℝ} {x : Space} (hx : ‖x‖ ≤ h) :
    (∫ y, coulombKernel (x-y)*radialShellDensity h y)=radialShellMoment h :=
  radial_coulomb_integral_inner (radialShellDensity_integrable h) (radialShellDensity_measurable h)
    (radialShellDensity_nonneg h) (radialShellDensity_le h) (radialShellDensity_radial h)
    (fun _ hz => radialShellDensity_zero_inner hz) hx

lemma radialShellMoment_lower {h : ℝ} (hh : 0 < h) :
    (∫ y, radialShellDensity h y)/(2*h) ≤ radialShellMoment h := by
  rw [div_eq_mul_inv,mul_comm,←integral_const_mul]
  apply integral_mono ((radialShellDensity_integrable h).const_mul _) (radialShellMoment_integrable h)
  intro y
  by_cases hy : y∈radialShell h
  · have hn : ‖y‖ < 2*h := by simpa only [Metric.mem_ball,dist_zero_right] using hy.1
    have hn0 : 0 < ‖y‖ := by
      have H : h ≤ ‖y‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hy.2
      exact hh.trans_le H
    exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (by positivity) hn0).mpr hn.le) (radialShellDensity_nonneg h y)
  · simp only [radialShellDensity,indicator_of_notMem hy,mul_zero,le_refl]

lemma radialShellMoment_pos {h : ℝ} (hh : 0 < h) : 0 < radialShellMoment h := by
  have H := radialShellMoment_lower hh
  rw [radialShellDensity_mass hh] at H
  exact lt_of_lt_of_le (by positivity) H

lemma atomicInnerField_shell_average {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) {h : ℝ} (_ : 0 < h) :
    (∫ y, atomicInnerField S ψ h y*radialShellDensity h y)=
      (totalCharge S-expectedPopulation ψ (Metric.ball 0 h))*radialShellMoment h := by
  have hAttr : Integrable (fun y => attraction S y*radialShellDensity h y) := by
    simp_rw [attraction_atomic S hatom,div_eq_mul_inv,mul_assoc]
    exact (radialShellMoment_integrable h).const_mul (totalCharge S)
  have hCore := restrictedCorePotential_mul_integrable ψ (A:=Metric.ball 0 h) measurableSet_ball _ (radialShellDensity_integrable h)
  simp only [atomicInnerField,sub_mul]
  rw [integral_sub hAttr hCore,restrictedCorePotential_fubini ψ measurableSet_ball _ (radialShellDensity_integrable h)]
  have ha : (∫ y, attraction S y*radialShellDensity h y)=totalCharge S*radialShellMoment h := by
    simp_rw [attraction_atomic S hatom,div_eq_mul_inv,mul_assoc]
    exact integral_const_mul _ _
  rw [ha]
  have hc : (∑ s : Spins n, ∑ i : Fin n, ∫ x, if position x i∈Metric.ball 0 h then
      (∫ y, coulombKernel (position x i-y)*radialShellDensity h y)*‖ψ.value s x‖^2 else 0)=
      expectedPopulation ψ (Metric.ball 0 h)*radialShellMoment h := by
    rw [expectedPopulation]
    simp only [Finset.sum_mul,←integral_mul_const]
    apply Finset.sum_congr rfl; intro s hs
    apply Finset.sum_congr rfl; intro i hi
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : position x i∈Metric.ball 0 h
    · have hn : ‖position x i‖ ≤ h := (by simpa only [Metric.mem_ball,dist_zero_right] using hx : ‖position x i‖ < h).le
      rw [ite_eq_left hx,integral_mul_const,radialShell_coulomb_inner hn,indicator_of_mem hx]
      ring
    · simp only [ite_eq_right hx,indicator_of_notMem hx,zero_mul]
  rw [hc]

end Coulomb
end

end
end

end OAI
