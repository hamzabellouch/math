import Mathlib
import OAI.Analysis.CoulombRadii.Localization.RadialCut
import OAI.Analysis.CoulombRadii.Localization.ThinCut

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

lemma thinCut_fderiv_zero (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b) (l : Fin 2)
    (x : Space) (hx : t+b < ‖x-y‖) : fderiv ℝ (thinCut y t b l) x=0 := by
  have he : thinCut y t b l =ᶠ[𝓝 x] (fun _ => if l=0 then (0:ℝ) else 1) := by
    have hh : ∀ᶠ z in 𝓝 x, t+b < ‖z-y‖ :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx
    filter_upwards [hh] with z hz
    simp only [thinCut,thinAngle_exterior y ht hb z hz.le,Real.sin_zero,Real.cos_zero]
  rw [he.fderiv_eq]
  simp

lemma thinCut_gradient_bound (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b) (i : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (thinCut y t b l) x (EuclideanSpace.single i 1))^2) ≤
      (2*(thinCutCoefficient/b)^2) * (Metric.closedBall y (t+b)).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x ∈ Metric.closedBall y (t+b)
  · rw [indicator_of_mem hx,mul_one]
    calc
      _ ≤ ∑ _l : Fin 2, (thinCutCoefficient/b)^2 := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg thinCutCoefficient_pos.le hb.le)).2
          (thinCut_derivative_bound y ht hb l i x)
      _ = _ := by simp
  · rw [indicator_of_notMem hx,mul_zero]
    have hd := thinCut_fderiv_zero y ht hb
    have hh : t+b < ‖x-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hx
    simp only [hd _ x hh,zero_apply,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,Finset.sum_const_zero,le_refl]

theorem form_thin_labelCut {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (thinCut y t b) (thinCut_smooth y t b)
      (thinCut_partition y t b) (thinCutCoefficient/b) (div_nonneg thinCutCoefficient_pos.le hb.le)
      (thinCut_derivative_bound y ht hb) p)) ≤
      form S ψ+3*(thinCutCoefficient/b)^2*expectedPopulation ψ (Metric.closedBall y (t+b)) := by
  rw [form_labelCut]
  apply add_le_add_right
  let c : ℝ := 2*(thinCutCoefficient/b)^2
  have hi s i := population_integrable ψ (Metric.closedBall y (t+b)) measurableSet_closedBall s i
  have H (s : Spins n) (a : Fin n × Fin 3) :
      (∫ x, (∑ l, (fderiv ℝ (thinCut y t b l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2) ≤
      c*(∫ x, (Metric.closedBall y (t+b)).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · filter_upwards [] with x
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    · exact (hi s a.1).const_mul c
    · filter_upwards [] with x
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_right (thinCut_gradient_bound y ht hb a.2 (position x a.1)) (sq_nonneg ‖ψ.value s x‖)
  calc
    _ ≤ (1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, c*(∫ x,
          (Metric.closedBall y (t+b)).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun a _ => H s a))) (by norm_num)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum,expectedPopulation,c]
      ring

end Coulomb
end

end
end

end OAI
