import OAI.Analysis.HenonEmden.CapOscillation

namespace OAI

universe uE

section CapContinuity

open MeasureTheory Set Metric Filter Topology
noncomputable section
namespace HenonLaneEmden.AdaptiveCap
open Cutoff CapWeights
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma weight_short_oscillation {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2) {x y : E} (hd : 0 < d x)
    (hxy : dist x y ≤ δ*(d x)^(m (Module.finrank ℝ E))) (e : sphere (0:E) 1) :
    |weight μ κ e x-weight μ κ e y| ≤
      oscillationConstant μ κ*δ*(d x)^(N (Module.finrank ℝ E)) := by
  let n := Module.finrank ℝ E
  have hn : 1 ≤ n := Module.finrank_pos
  have hdist : dist x y ≤ d x/2 := by
    have hp := pow_d_le_self x (show 1 ≤ m n by unfold m; omega)
    calc
      _ ≤ δ*(d x)^(m n) := hxy
      _ ≤ δ*d x := mul_le_mul_of_nonneg_left hp hδ
      _ ≤ _ := by nlinarith
  have hh := weight_close_oscillation μ hκ hκ1 hd hdist e
  have hc := oscillationConstant_nonneg μ hκ.le
  calc
    _ ≤ oscillationConstant μ κ*(d x)^(N n-n-1)*dist x y := hh
    _ ≤ oscillationConstant μ κ*(d x)^(N n-n-1)*(δ*(d x)^(m n)) :=
      mul_le_mul_of_nonneg_left hxy (mul_nonneg hc (pow_nonneg hd.le _))
    _ = oscillationConstant μ κ*δ*(d x)^((N n-n-1)+m n) := by rw [pow_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hδ)
      exact pow_le_pow_of_le_one hd.le (d_le_one x) (by change (k n) + n + 2 ≤ (k n + n + 2 - n - 1) + (n+3); omega)

lemma continuous_weight {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:E) 1) :
    Continuous (weight μ κ e) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hd : 0 < d x
  · rw [Metric.continuousAt_iff]
    intro ε hε
    let C := oscillationConstant μ κ*(d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E-1)
    have hC : 0 ≤ C := mul_nonneg (oscillationConstant_nonneg μ hκ.le) (pow_nonneg hd.le _)
    have hC1 : 0 < C+1 := by linarith
    refine ⟨min (d x/2) (ε/(C+1)),lt_min (half_pos hd) (div_pos hε hC1),?_⟩
    intro y hy
    have hdist : dist x y < ε/(C+1) := by simpa only [dist_comm x y] using (lt_min_iff.mp hy).2
    have hh := weight_close_oscillation μ hκ hκ1 hd (y := y)
      (by simpa only [dist_comm] using (lt_min_iff.mp hy).1.le) e
    change |weight μ κ e x-weight μ κ e y| ≤ C*dist x y at hh
    rw [Real.dist_eq,abs_sub_comm]
    have hb : (C+1)*dist x y < ε := by simpa only [mul_comm] using (lt_div_iff₀ hC1).mp hdist
    have hr := dist_nonneg (x := x) (y := y)
    nlinarith
  · have hd0 : d x = 0 := le_antisymm (not_lt.mp hd) (d_nonneg x)
    have hx : 2 ≤ ‖x‖ := not_lt.mp (fun hh => hd ((d_pos_iff x).mpr hh))
    have hN : N (Module.finrank ℝ E)-Module.finrank ℝ E ≠ 0 := by unfold N; omega
    have hcont : Continuous (fun y : E => boundConstant μ κ*(d y)^(N (Module.finrank ℝ E)-Module.finrank ℝ E)) :=
      continuous_const.mul (continuous_d.pow _)
    have ht : Tendsto (fun y : E => boundConstant μ κ*(d y)^(N (Module.finrank ℝ E)-Module.finrank ℝ E))
        (𝓝 x) (𝓝 0) := by simpa only [hd0,zero_pow hN,mul_zero] using hcont.tendsto x
    change Tendsto _ (𝓝 x) (𝓝 (weight μ κ e x))
    rw [weight_outer μ κ e hx]
    exact squeeze_zero (weight_nonneg μ κ e) (weight_bound μ hκ hκ1 e) ht

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma continuous_weight_direction (κ : ℝ) (x : E) :
    Continuous (fun e : sphere (0:E) 1 => weight μ κ e x) := by
  by_cases hx : x ≠ 0 ∧ 0 < d x
  · simp only [weight,dite_eq_left hx,normalized]
    exact continuous_const.mul ((continuous_profile _ _).div_const _)
  · simp only [weight,dite_eq_right hx]; exact continuous_const

lemma measurable_weight {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    Measurable (fun z : sphere (0:E) 1 × E => weight μ κ z.1 z.2) := by
  have hh : Measurable (fun z : E × sphere (0:E) 1 => weight μ κ z.2 z.1) :=
    measurable_uncurry_of_continuous_of_measurable (continuous_weight μ hκ hκ1)
      (fun x => (continuous_weight_direction μ κ x).measurable)
  exact hh.comp measurable_swap

lemma weight_le_constant {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:E) 1) (x : E) :
    weight μ κ e x ≤ boundConstant μ κ := by
  apply (weight_bound μ hκ hκ1 e x).trans
  have hp := pow_le_one₀ (d_nonneg x) (d_le_one x) (n := N (Module.finrank ℝ E)-Module.finrank ℝ E)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (boundConstant_nonneg μ hκ.le)

end HenonLaneEmden.AdaptiveCap
end
end CapContinuity

end OAI
