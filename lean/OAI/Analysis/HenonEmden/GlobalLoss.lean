import OAI.Analysis.HenonEmden.LayerIntegration

namespace OAI

universe uE

section GlobalLoss

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents Angular LayerTonelli
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def lossCoefficient (κ δ M P : ℝ) : ℝ :=
  oscillationConstant μ κ*δ*μ.toSphere.real univ+
    (boundConstant μ κ*rayConstant (Module.finrank ℝ E)*M)/δ^(Module.finrank ℝ E)/P

def lowLevelConstant (n : ℕ) : ℝ := 6*(N n:ℝ)*3^(N n-1)
lemma lowLevelConstant_nonneg (n : ℕ) : 0 ≤ lowLevelConstant n := by unfold lowLevelConstant; positivity
omit [BorelSpace E] [Nontrivial E] in
lemma lossCoefficient_nonneg {κ δ M P : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hP : 0 ≤ P) :
    0 ≤ lossCoefficient μ κ δ M P := by
  have hO := oscillationConstant_nonneg μ hκ
  have hC := boundConstant_nonneg μ hκ
  have hR : 0 ≤ rayConstant (Module.finrank ℝ E) := by unfold rayConstant; positivity
  unfold lossCoefficient
  positivity

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma averagedLoss_zero_outer (f : E → ℝ) (κ δ : ℝ) {x : E} (hx : 2 ≤ ‖x‖) (t : ℝ) :
    averagedLoss μ f κ δ (x,t)=0 := by
  unfold averagedLoss
  apply integral_eq_zero_of_ae
  filter_upwards [] with e
  rw [weight_outer μ κ e hx]
  have he := lineWeight_le μ f κ δ (e,x,t)
  rw [weight_outer μ κ e hx] at he
  rw [le_antisymm he (lineWeight_nonneg μ f κ δ _)]
  simp

lemma lintegral_averagedLoss_bound {f u : E → ℝ} (hf : Measurable f) (hu : Measurable u)
    (hfo : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) (hfn : ∀ x, 0 ≤ f x) (hun : ∀ x, 0 ≤ u x)
    {κ δ M P : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hM : 0 ≤ M) (hP : 0 < P)
    (hm : (∫⁻ x in ball (0:E) 4, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal M) :
    (∫⁻ z, ENNReal.ofReal (u z.1*averagedLoss μ f κ δ z) ∂layerMeasure μ f) ≤
      ENNReal.ofReal (lossCoefficient μ κ δ M P)*
        (∫⁻ x, ENNReal.ofReal (eta (Module.finrank ℝ E) x*f x*u x) ∂μ)+
      ENNReal.ofReal (lowLevelConstant (Module.finrank ℝ E)*P)*
        ∫⁻ x in ball (0:E) 2, ENNReal.ofReal (u x) ∂μ := by
  let n := Module.finrank ℝ E
  let c := lossCoefficient μ κ δ M P
  have hc : 0 ≤ c := lossCoefficient_nonneg μ hκ.le hδ.le hM hP.le
  have hcP : 0 ≤ lowLevelConstant n*P := mul_nonneg (lowLevelConstant_nonneg n) hP.le
  have hla := measurable_averagedLoss μ hfo hκ hκ1 δ
  have hetaM : Measurable (eta (Module.finrank ℝ E) : E → ℝ) := (continuous_eta _).measurable
  rw [lintegral_layerMeasure μ hf (by fun_prop)]
  simp_rw [ENNReal.ofReal_mul (hun _)]
  have hfactor (x : E) :
      (∫⁻ t in Ioo 0 (f x), ENNReal.ofReal (u x)*ENNReal.ofReal (averagedLoss μ f κ δ (x,t))) =
      ENNReal.ofReal (u x)*(∫⁻ t in Ioo 0 (f x), ENNReal.ofReal (averagedLoss μ f κ δ (x,t))) :=
    lintegral_const_mul _ (by fun_prop)
  simp_rw [hfactor]
  have hpoint (x : E) :
      ENNReal.ofReal (u x)*(∫⁻ t in Ioo 0 (f x), ENNReal.ofReal (averagedLoss μ f κ δ (x,t))) ≤
      ENNReal.ofReal c*ENNReal.ofReal (eta n x*f x*u x)+
      (ball (0:E) 2).indicator (fun x => ENNReal.ofReal (lowLevelConstant n*P)*ENNReal.ofReal (u x)) x := by
    by_cases hx : x ∈ ball (0:E) 2
    · have hd : 0 < d x := (d_pos_iff x).mpr (mem_ball_zero_iff.mp hx)
      have hh := integrated_averagedLoss μ hfo hκ hκ1 hδ hδ1 hd (hfn x) hM hP hm
      have hh' := mul_le_mul (le_refl (ENNReal.ofReal (u x))) hh bot_le bot_le
      rw [indicator_of_mem hx]
      apply hh'.trans
      have heta0 : 0 ≤ eta n x := le_trans (pow_nonneg (d_nonneg x) _) (etaProfile_bounds n ‖x‖).1
      rw [← ENNReal.ofReal_mul (hun x),← ENNReal.ofReal_mul hc,
        ← ENNReal.ofReal_mul hcP,← ENNReal.ofReal_add
          (mul_nonneg hc (mul_nonneg (mul_nonneg heta0 (hfn x)) (hun x)))
          (mul_nonneg hcP (hun x))]
      apply ENNReal.ofReal_le_ofReal
      have heta : (d x)^(N n) ≤ eta n x := (etaProfile_bounds n ‖x‖).1
      change u x*(c*(d x)^(N n)*f x+lowLevelConstant n*P) ≤ _
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heta hc) (hfn x)) (hun x)]
    · have hx' : 2 ≤ ‖x‖ := not_lt.mp (by simpa only [mem_ball,dist_zero_right] using hx)
      simp_rw [averagedLoss_zero_outer μ f κ δ hx']
      simp only [ENNReal.ofReal_zero,lintegral_zero,mul_zero]
      exact bot_le
  apply (lintegral_mono hpoint).trans_eq
  rw [lintegral_add_left (by fun_prop),lintegral_indicator measurableSet_ball,
    lintegral_const_mul _ (by fun_prop),lintegral_const_mul _ hu.ennreal_ofReal]

end HenonLaneEmden.SpatialComponents
end
end GlobalLoss

end OAI
