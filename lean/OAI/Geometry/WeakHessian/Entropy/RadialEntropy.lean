import Mathlib
import OAI.Geometry.WeakHessian.Measure.RadialCutoff
import OAI.Geometry.WeakHessian.Entropy.ZeroDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile30
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

lemma mul_log_product (a b : ℝ) :
    (a*b)*Real.log (a*b) = a*(b*Real.log b)+b*(a*Real.log a) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Real.log_mul ha hb]
  ring

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma entropy_integral_multipliers_tendsto {ρ : X → ℝ}
    (hρ : Integrable ρ m) (hE : Integrable (fun x => ρ x*Real.log (ρ x)) m)
    {a : ℕ → X → ℝ} (ha : ∀ n, AEStronglyMeasurable (a n) m)
    {A : ℝ} (_hA : 0 ≤ A) (haA : ∀ n, ∀ᵐ x ∂m, a n x ∈ Icc 0 A)
    (haT : ∀ᵐ x ∂m, Tendsto (fun n => a n x) atTop (𝓝 1)) :
    (∀ n, Integrable (fun x => (a n x*ρ x)*Real.log (a n x*ρ x)) m) ∧
    Tendsto (fun n => ∫ x,(a n x*ρ x)*Real.log (a n x*ρ x) ∂m) atTop
      (𝓝 (∫ x,ρ x*Real.log (ρ x) ∂m)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := A)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  let B (x : X) := A*|ρ x*Real.log (ρ x)|+C*|ρ x|
  have hBi : Integrable B m := hE.abs.const_mul A |>.add (hρ.abs.const_mul C)
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => (a n x*ρ x)*Real.log (a n x*ρ x)) m :=
    Real.continuous_mul_log.comp_aestronglyMeasurable ((ha n).mul hρ.1)
  have hb (n : ℕ) : ∀ᵐ x ∂m, ‖(a n x*ρ x)*Real.log (a n x*ρ x)‖ ≤ B x := by
    filter_upwards [haA n] with x hx
    rw [mul_log_product,Real.norm_eq_abs]
    apply (abs_add_le _ _).trans
    dsimp [B]
    simp only [abs_mul,abs_of_nonneg hx.1]
    exact add_le_add (mul_le_mul_of_nonneg_right hx.2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      (by simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hx.1,mul_comm] using mul_le_mul_of_nonneg_left (hC _ hx) (abs_nonneg (ρ x)))
  refine ⟨fun n => hBi.mono' (hm n) (hb n),?_⟩
  apply tendsto_integral_of_dominated_convergence B hm hBi hb
  filter_upwards [haT] with x hx
  have ht : Tendsto (fun n => a n x*ρ x) atTop (𝓝 (ρ x)) := by simpa using hx.mul_const (ρ x)
  exact (Real.continuous_mul_log.tendsto (ρ x)).comp ht

lemma squareDensity_entropy_eq [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    [IsFiniteMeasure (squareDensityMeasure m w)] :
    entropyReal m (squareDensityMeasure m w) = ∫ x,w x^2*Real.log (w x^2) ∂m := by
  have hac : squareDensityMeasure m w ≪ m := withDensity_absolutelyContinuous _ _
  rw [entropyReal_eq_integral_density hac]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity m (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)] with x hx
  simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]

lemma squareDensity_finiteEntropy_iff [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    [IsFiniteMeasure (squareDensityMeasure m w)] :
    FiniteEntropy m (squareDensityMeasure m w) ↔ Integrable (fun x => w x^2*Real.log (w x^2)) m := by
  have hac : squareDensityMeasure m w ≪ m := withDensity_absolutelyContinuous _ _
  rw [FiniteEntropy,and_iff_right hac,← integrable_rnDeriv_mul_log_iff hac]
  apply integrable_congr
  filter_upwards [Measure.rnDeriv_withDensity m (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)] with x hx
  simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]

variable [MetricSpace X] [BorelSpace X]

lemma normalized_radial_entropy_tendsto [SigmaFinite m] {w : X → ℝ}
    (hw : MemLp w 2 m) (hwm : Measurable w) [IsProbabilityMeasure (squareDensityMeasure m w)]
    (hE : FiniteEntropy m (squareDensityMeasure m w)) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 2) (hcT : Tendsto c atTop (𝓝 1))
    (hp : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)))) :
    (∀ n, FiniteEntropy m (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)))) ∧
    Tendsto (fun n => entropyReal m (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x))))
      atTop (𝓝 (entropyReal m (squareDensityMeasure m w))) := by
  let a (n : ℕ) (x : X) := (c n*radialCutoff o (n+k) x)^2
  have ha n : AEStronglyMeasurable (a n) m := by
    exact (((radialCutoff_lipschitz o (n+k)).continuous.const_mul (c n)).pow 2).aestronglyMeasurable
  have hA n : ∀ᵐ x ∂m, a n x ∈ Icc (0:ℝ) 4 := by
    apply ae_of_all
    intro x
    have hn : 0 ≤ c n*radialCutoff o (n+k) x := mul_nonneg (hc n).1 (radialCutoff_nonneg o (n+k) x)
    have hb : c n*radialCutoff o (n+k) x ≤ 2 :=
      (mul_le_of_le_one_right (hc n).1 (radialCutoff_le_one o (n+k) x)).trans (hc n).2
    exact ⟨sq_nonneg _,by dsimp [a]; nlinarith⟩
  have haT : ∀ᵐ x ∂m, Tendsto (fun n => a n x) atTop (𝓝 1) := ae_of_all _ fun x => by
    simpa only [one_mul,one_pow,a,Function.comp_apply] using (hcT.mul ((radialCutoff_tendsto o x).comp (tendsto_add_atTop_nat k))).pow 2
  have he (n : ℕ) (x : X) : (c n*(w x*radialCutoff o (n+k) x))^2 = a n x*w x^2 := by dsimp [a]; ring
  have H := entropy_integral_multipliers_tendsto hw.integrable_sq
    ((squareDensity_finiteEntropy_iff hwm).mp hE) ha (by norm_num : (0:ℝ) ≤ 4) hA haT
  have hm (n : ℕ) : Measurable (fun x => c n*(w x*radialCutoff o (n+k) x)) :=
    (hwm.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable).const_mul _
  constructor
  · intro n
    let := hp n
    apply (squareDensity_finiteEntropy_iff (hm n)).mpr
    simpa only [he] using H.1 n
  · have eqn (n : ℕ) : entropyReal m (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x))) =
        ∫ x,(a n x*w x^2)*Real.log (a n x*w x^2) ∂m := by
      let := hp n
      rw [squareDensity_entropy_eq (hm n)]
      simp only [he]
    simp_rw [eqn,squareDensity_entropy_eq hwm]
    exact H.2
end WeakHessian

end
end InlinedFile30

end OAI
