import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ReweightCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile62
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma squareDensity_const_mul {w : X → ℝ} (hw : Measurable w) (c : ℝ) :
    squareDensityMeasure m (fun x => c*w x) = ENNReal.ofReal (c^2) • squareDensityMeasure m w := by
  unfold squareDensityMeasure
  rw [← withDensity_smul _ (hw.pow_const 2 |>.ennreal_ofReal)]
  congr 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _)]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma squareDensity_radial_le {w : X → ℝ} (o : X) (n : ℕ) :
    squareDensityMeasure m (fun x => w x*radialCutoff o n x) ≤ squareDensityMeasure m w := by
  apply withDensity_mono
  exact ae_of_all _ fun x => by
    apply ENNReal.ofReal_le_ofReal
    have h1 := radialCutoff_nonneg o n x
    have h2 := radialCutoff_le_one o n x
    have hc : radialCutoff o n x^2 ≤ 1 := by nlinarith
    rw [mul_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (sq_nonneg (w x))

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma squareDensity_normalized_radial_support [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    (o : X) (n : ℕ) (c : ℝ) :
    (squareDensityMeasure m (fun x => c*(w x*radialCutoff o n x)))
      (Metric.closedBall o ((n:ℝ)+1))ᶜ = 0 := by
  apply ae_iff.mp
  apply squareDensity_ae_support ((hw.mul (radialCutoff_lipschitz o n).continuous.measurable).const_mul c)
  exact ae_of_all _ fun x hx => by
    have hdn : (n:ℝ)+1 ≤ dist x o := (not_le.mp hx).le
    have hz : radialCutoff o n x = 0 := by
      unfold radialCutoff
      rw [max_eq_left]
      exact sub_nonpos.mpr ((le_div_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr (by simpa using hdn))
    change c*(w x*radialCutoff o n x)=0
    simp only [hz,mul_zero]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma squareDensity_normalized_radial_le {w : X → ℝ} (hw : Measurable w)
    (o : X) (n : ℕ) {c : ℝ} (hc : |c| ≤ 2) :
    squareDensityMeasure m (fun x => c*(w x*radialCutoff o n x)) ≤
      (4:ℝ≥0∞) • squareDensityMeasure m w := by
  rw [squareDensity_const_mul (w := fun x => w x*radialCutoff o n x) (hw.mul (radialCutoff_lipschitz o n).continuous.measurable) c]
  apply (_root_.smul_le_smul_left _ (squareDensity_radial_le (m := m) (w := w) o n)).trans
  apply IsOrderedSMul.smul_le_smul_right
  have hs : c^2 ≤ 4 := by nlinarith [sq_abs c,abs_nonneg c]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

omit [ProperSpace X] in
lemma radial_secondMoment_tendsto {w : X → ℝ} (hw : Measurable w) (o : X) (k : ℕ)
    (hM : Integrable (fun x => dist x o^2) (squareDensityMeasure m w)) :
    Tendsto (fun n : ℕ => ∫ x,dist x o^2 ∂squareDensityMeasure m (fun x => w x*radialCutoff o (n+k) x))
      atTop (𝓝 (∫ x,dist x o^2 ∂squareDensityMeasure m w)) := by
  have he (n : ℕ) : (∫ x,dist x o^2 ∂squareDensityMeasure m (fun x => w x*radialCutoff o (n+k) x)) =
      ∫ x,(w x*radialCutoff o (n+k) x)^2*dist x o^2 ∂m :=
    squareDensity_integral (hw.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable) (fun x => dist x o^2)
  simp only [he,squareDensity_integral hw]
  have hi := (squareDensity_integrable hw).mp hM
  apply tendsto_integral_of_dominated_convergence (fun x => w x^2*dist x o^2)
    (fun n => (((hw.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable).pow_const 2).mul
      ((measurable_id.dist measurable_const).pow_const 2)).aestronglyMeasurable) hi
  · intro n
    exact ae_of_all _ fun x => by
      change ‖(w x*radialCutoff o (n+k) x)^2*dist x o^2‖ ≤ w x^2*dist x o^2
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),mul_pow]
      have h1 := radialCutoff_nonneg o (n+k) x
      have h2 := radialCutoff_le_one o (n+k) x
      have hc : radialCutoff o (n+k) x^2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (w x)) (sq_nonneg (dist x o)),
        mul_le_mul_of_nonneg_left hc (mul_nonneg (sq_nonneg (w x)) (sq_nonneg (dist x o)))]
  · exact ae_of_all _ fun x => by
      have H := ((((radialCutoff_tendsto o x).comp (tendsto_add_atTop_nat k)).const_mul (w x)).pow 2).mul_const (dist x o^2)
      simpa only [mul_one,Function.comp_apply,Pi.mul_apply,id_eq] using H

lemma normalized_radial_cost_tendsto {w : X → ℝ} (hw : Measurable w)
    (μ : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (k : ℕ) {c : ℕ → ℝ} (hc : ∀ n,0 < c n) (hcT : Tendsto c atTop (𝓝 1))
    (ν : ℕ → ProbabilityMeasure X)
    (hν : ∀ n,(ν n:Measure X) = squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)))
    (hM : Integrable (fun x => dist x o^2) (μ:Measure X)) :
    (∀ n,Integrable (fun x => dist x o^2) (ν n:Measure X)) ∧
    Tendsto (fun n => quadraticWassersteinSq (μ:Measure X) (ν n:Measure X)) atTop (𝓝 0) := by
  let σ (n : ℕ) : Measure X := squareDensityMeasure m (fun x => w x*radialCutoff o (n+k) x)
  have hσ (n) : σ n ≤ (μ:Measure X) := by rw [hμ]; exact squareDensity_radial_le o (n+k)
  let (n : ℕ) : IsFiniteMeasure (σ n) := isFiniteMeasure_of_le (μ:Measure X) (hσ n)
  have he (n) : (ν n:Measure X) = ENNReal.ofReal (c n^2) • σ n := by
    rw [hν n]; exact squareDensity_const_mul (hw.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable) (c n)
  have hi (n) : Integrable (fun x => dist x o^2) (ν n:Measure X) := by
    rw [he n]; exact (hM.mono_measure (hσ n)).smul_measure ENNReal.ofReal_ne_top
  refine ⟨hi,?_⟩
  let ρ (n : ℕ) : Measure X := (μ:Measure X)-σ n
  let (n : ℕ) : IsFiniteMeasure (ρ n) := isFiniteMeasure_of_le (μ:Measure X) Measure.sub_le
  let a (n : ℕ) : ℝ≥0∞ := (ENNReal.ofReal (c n^2))⁻¹
  have hc0 (n) : ENNReal.ofReal (c n^2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos (hc n))
  have hae (n) : a n • (ν n:Measure X) = σ n := by
    rw [he n,smul_smul]
    simp only [a,ENNReal.inv_mul_cancel (hc0 n) ENNReal.ofReal_ne_top,one_smul]
  apply quadraticWassersteinSq_reweight_tendsto μ ν ρ a
    (fun n => ENNReal.inv_ne_top.mpr (hc0 n)) (fun n => ?_) o hM hi
  · have H := (hcT.pow 2).inv₀ (by norm_num : (1:ℝ)^2 ≠ 0)
    simpa only [a,ENNReal.toReal_inv,ENNReal.toReal_ofReal (sq_nonneg _),one_pow,inv_one] using H
  · have HT := radial_secondMoment_tendsto hw o k (hμ ▸ hM)
    have H := (hcT.pow 2).mul HT
    have eqn (n) : (∫ x,dist x o^2 ∂(ν n:Measure X)) = c n^2*(∫ x,dist x o^2 ∂σ n) := by
      rw [he n,integral_smul_measure,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
    simp_rw [eqn]
    simpa only [hμ,one_pow,one_mul,σ] using H
  · rw [hae n]
    exact (add_comm (σ n) (ρ n)).trans (Measure.sub_add_cancel_of_le (hσ n)) |>.symm
end WeakHessian

end
end InlinedFile62

end OAI
