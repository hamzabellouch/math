import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.Multiplier
import OAI.Geometry.CAT0Fillings.Sobolev.CriticalNorm
import OAI.Geometry.CAT0Fillings.Powers.Slope

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_abs_rpow {f : α → ℝ} {p r : ℝ} (hr : 0 < r)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x => |f x|^r) (ENNReal.ofReal (p/r)) μ := by
  simpa only [Real.norm_eq_abs,ENNReal.toReal_ofReal hr.le,ENNReal.ofReal_div_of_pos hr]
    using hf.norm_rpow_div (ENNReal.ofReal r)

lemma potential_holder_conjugate {p : ℝ} (hp : 2 < p) :
    (p/(p-2)).HolderConjugate (p/2) := by
  apply Real.holderConjugate_iff.mpr
  refine ⟨(lt_div_iff₀ (by linarith : 0 < p-2)).mpr (by linarith),?_⟩
  field_simp
  ring

lemma potential_integrable {f g : α → ℝ} {p : ℝ} (hp : 2 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    Integrable (fun x => |f x|^(p-2)*(g x)^2) μ := by
  have := (potential_holder_conjugate hp).ennrealOfReal
  have hh := (memLp_abs_rpow (by linarith : 0 < p-2) hf).integrable_mul
    (memLp_abs_rpow (by norm_num : (0:ℝ) < 2) hg)
  convert hh using 1
  ext x
  simp only [Pi.mul_apply,Real.rpow_two,sq_abs]

lemma potential_holder {f g : α → ℝ} {p : ℝ} (hp : 2 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x, |f x|^(p-2)*(g x)^2 ∂μ) ≤
      (∫ x, |f x|^p ∂μ)^((p-2)/p) * (lpNorm g (ENNReal.ofReal p) μ)^2 := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (potential_holder_conjugate hp)
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (f x)) (p-2))
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (g x)) (2:ℝ))
    (memLp_abs_rpow hpm hf) (memLp_abs_rpow (by norm_num : (0:ℝ) < 2) hg)
  have he1 : (p-2)*(p/(p-2)) = p := by field_simp
  have he2 : (2:ℝ)*(p/2) = p := by ring
  have he3 : (1:ℝ)/(p/(p-2)) = (p-2)/p := by field_simp
  have he4 : (1:ℝ)/(p/2) = 2/p := by field_simp
  change (∫ x, |f x|^(p-2)*|g x|^(2:ℝ) ∂μ) ≤
    (∫ x, (|f x|^(p-2))^(p/(p-2)) ∂μ)^(1/(p/(p-2))) *
    (∫ x, (|g x|^(2:ℝ))^(p/2) ∂μ)^(1/(p/2)) at hh
  simp only [←Real.rpow_mul (abs_nonneg _),he1,he2,he3,he4] at hh
  simp only [Real.rpow_two,sq_abs] at hh
  rw [AnalyticMinimizer.lpNorm_sq_eq_integral hp0 hg.aestronglyMeasurable]
  exact hh

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma truncated_gradient_energy (P Q R : q.Sobolev) {γ N : ℝ}
    (hγ : 1 < γ) (hN : 0 < N)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hQ : (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope γ N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w))
    (hR : (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope (2*γ-1) N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w)) :
    (2*γ-1)/γ^2*‖q.closedGradient Q‖^2 ≤ inner ℝ (q.closedGradient P) (q.closedGradient R) := by
  rw [l2_norm_sq,L2.inner_def,←integral_const_mul]
  apply integral_mono_ae (((Lp.memLp (q.closedGradient Q)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul _)
    (L2.integrable_inner _ _)
  filter_upwards [hQ,hR,q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => 0 ≤ q.inclusion P x) hP] with w hQ hR hP
  rw [hQ,hR,inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (truncatedPowerSlope_ratio hγ hN hP)
    (sq_nonneg ‖q.closedGradient P w‖)

lemma truncated_power_energy (_hz : IsCycle T) (P Q R : q.Sobolev) {γ N p A n : ℝ}
    (hγ : 1 < γ) (hN : 0 < N) (hp : 2 < p) (hA : 0 ≤ A) (hn : 0 ≤ n)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hQv : (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => truncatedPower γ N (q.inclusion P x)))
    (hRv : (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => truncatedPower (2*γ-1) N (q.inclusion P x)))
    (hQ : (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope γ N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w))
    (hR : (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope (2*γ-1) N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w))
    (heuler : A*inner ℝ (q.closedGradient P) (q.closedGradient R) + n*inner ℝ (q.inclusion P) (q.inclusion R) =
      n*(∫ x, (q.inclusion P x)^(p-1)*q.inclusion R x ∂MassMeasure.currentMassMeasure hT)) :
    A*((2*γ-1)/γ^2)*‖q.closedGradient Q‖^2 ≤
      n*(∫ x, |q.inclusion P x|^(p-2)*(q.inclusion Q x)^2 ∂MassMeasure.currentMassMeasure hT) := by
  have hgrad := mul_le_mul_of_nonneg_left (q.truncated_gradient_energy P Q R hγ hN hP hQ hR) hA
  have hzI : 0 ≤ inner ℝ (q.inclusion P) (q.inclusion R) := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hP,hRv] with x hx hR
    rw [hR,real_inner_comm]
    exact mul_nonneg hx (truncatedPower_nonneg hN.le)
  have he : (∫ x, (q.inclusion P x)^(p-1)*q.inclusion R x ∂MassMeasure.currentMassMeasure hT) =
      (∫ x, |q.inclusion P x|^(p-2)*(q.inclusion Q x)^2 ∂MassMeasure.currentMassMeasure hT) := by
    apply integral_congr_ae
    filter_upwards [hP,hRv,hQv] with x hx hR hQ
    rw [hR,hQ,abs_of_nonneg hx]
    exact truncatedPower_rhs hγ hN hx hp
  rw [he] at heuler
  have hzprod := mul_nonneg hn hzI
  nlinarith

end CAT0Fillings.ChartGeometry
end

end OAI
