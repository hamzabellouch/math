import OAI.Analysis.HenonEmden.CutoffOscillation

namespace OAI

universe uE

section AdaptiveCaps

open MeasureTheory Set Metric NormedSpace
noncomputable section
namespace HenonLaneEmden.AdaptiveCap
open Cutoff CapWeights

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def direction (x : E) (hx : x ≠ 0) : sphere (0:E) 1 :=
  ⟨NormedSpace.normalize x, by simpa only [mem_sphere,dist_zero_right] using NormedSpace.norm_normalize hx⟩

def weight (κ : ℝ) (e : sphere (0:E) 1) (x : E) : ℝ := by
  classical
  exact if hx : x ≠ 0 ∧ 0 < d x then
    w (Module.finrank ℝ E) x * normalized μ.toSphere (direction x hx.1) (κ*d x) e
  else 0

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma w_nonneg (n : ℕ) (x : E) : 0 ≤ w n x := by
  rw [w_eq_profile]; exact wProfile_nonneg n (norm_nonneg x)
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma w_inner (n : ℕ) {x : E} (hx : ‖x‖ ≤ 1) : w n x = 0 := by
  rw [w_eq_profile,wProfile,derivativeProfile_inner n hx,mul_zero]
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma w_outer (n : ℕ) {x : E} (hx : 2 ≤ ‖x‖) : w n x = 0 := by
  rw [w_eq_profile,wProfile,derivativeProfile_outer n hx,mul_zero]
omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma weight_nonneg (κ : ℝ) (e : sphere (0:E) 1) (x : E) : 0 ≤ weight μ κ e x := by
  unfold weight
  split_ifs
  · exact mul_nonneg (w_nonneg _ _) (normalized_nonneg _ _ _ _)
  · rfl
omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma weight_inner (κ : ℝ) (e : sphere (0:E) 1) {x : E} (hx : ‖x‖ ≤ 1) :
    weight μ κ e x = 0 := by
  unfold weight
  split_ifs <;> simp [w_inner _ hx]
omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma weight_outer (κ : ℝ) (e : sphere (0:E) 1) {x : E} (hx : 2 ≤ ‖x‖) :
    weight μ κ e x = 0 := by
  unfold weight
  split_ifs <;> simp [w_outer _ hx]

lemma integral_weight {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (x : E) :
    (∫ e, weight μ κ e x ∂μ.toSphere) = w (Module.finrank ℝ E) x := by
  by_cases hx : x ≠ 0 ∧ 0 < d x
  · simp only [weight,dite_eq_left hx,integral_const_mul]
    rw [integral_normalized _ (ne_of_gt (sphere_normalizer_pos μ _ (mul_pos hκ hx.2)
      ((mul_le_of_le_one_left (d_nonneg x) hκ1).trans (d_le_one x)))),mul_one]
  · have hw : w (Module.finrank ℝ E) x = 0 := by
      by_cases hx0 : x = 0
      · subst x; exact w_inner _ (by simp)
      · exact w_outer _ (not_lt.mp (fun hh => hx ⟨hx0,(d_pos_iff x).mpr hh⟩))
    simp only [weight,dite_eq_right hx,integral_zero,hw]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma normalize_dist_le {x y : E} (hx : 1/2 ≤ ‖x‖) (hy : 1/2 ≤ ‖y‖) :
    dist (NormedSpace.normalize x) (NormedSpace.normalize y) ≤ 4*dist x y := by
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt (by linarith)
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖y‖))
  have he : NormedSpace.normalize x-NormedSpace.normalize y =
      ‖x‖⁻¹ • (x-y) + ((‖y‖-‖x‖)/‖x‖) • NormedSpace.normalize y := by
    rw [NormedSpace.normalize,NormedSpace.normalize,smul_sub,smul_smul]
    have hr : (‖y‖-‖x‖)/‖x‖*‖y‖⁻¹ = ‖x‖⁻¹-‖y‖⁻¹ := by
      field_simp [hx0,norm_ne_zero_iff.mpr hy0]
    rw [hr,sub_smul]
    abel
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖‖x‖⁻¹ • (x-y)‖+‖((‖y‖-‖x‖)/‖x‖) • NormedSpace.normalize y‖ := norm_add_le _ _
    _ = (dist x y+|‖y‖-‖x‖|)/‖x‖ := by
      rw [norm_smul,norm_smul,NormedSpace.norm_normalize hy0,mul_one,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg x),abs_div,
        abs_of_nonneg (norm_nonneg x),← dist_eq_norm]
      ring
    _ ≤ (dist x y+dist x y)/‖x‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg x)
      gcongr
      simpa only [dist_comm x y,dist_eq_norm] using abs_norm_sub_norm_le y x
    _ ≤ (dist x y+dist x y)/(1/2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hx
    _ = _ := by ring

def boundConstant (κ : ℝ) : ℝ :=
  (6*(N (Module.finrank ℝ E):ℝ)*3^(N (Module.finrank ℝ E)-1)) /
    (lowerConstant μ * κ^(Module.finrank ℝ E-1))

omit [BorelSpace E] [Nontrivial E] in
lemma boundConstant_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ boundConstant μ κ := by
  unfold boundConstant
  exact div_nonneg (by positivity) (mul_nonneg (constants_positive μ).1.le (pow_nonneg hκ _))

lemma weight_bound {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:E) 1) (x : E) :
    weight μ κ e x ≤ boundConstant μ κ * (d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E) := by
  let n := Module.finrank ℝ E
  have hn : 1 ≤ n := Module.finrank_pos
  by_cases hx : x ≠ 0 ∧ 0 < d x
  · rw [weight,dite_eq_left hx]
    have hrad : κ*d x ≤ 1 := (mul_le_of_le_one_left (d_nonneg x) hκ1).trans (d_le_one x)
    have hb := (sphere_normalizer_bounds μ (direction x hx.1) (mul_pos hκ hx.2) hrad).1
    have hc : 0 < lowerConstant μ*κ^(n-1) := mul_pos (constants_positive μ).1 (pow_pos hκ _)
    have hpow : n-1+(N n-n) = N n-1 := by dsimp [N]; omega
    calc
      _ ≤ (6*(N n:ℝ)*3^(N n-1)*(d x)^(N n-1)) *
          (1/(lowerConstant μ*(κ*d x)^(n-1))) := by
        apply mul_le_mul
        · rw [w_eq_profile]; exact wProfile_bound n (norm_nonneg x)
        · exact (normalized_le_inv μ.toSphere _ (mul_pos hκ hx.2) e).trans
            (by simpa only [one_div] using one_div_le_one_div_of_le (mul_pos (constants_positive μ).1 (pow_pos (mul_pos hκ hx.2) _)) hb)
        · exact normalized_nonneg _ _ _ _
        · exact mul_nonneg (by positivity) (pow_nonneg (d_nonneg x) _)
      _ = _ := by
        have hdPow : (d x)^(N n-1) = (d x)^(n-1)*(d x)^(N n-n) := by rw [← hpow,pow_add]
        rw [hdPow,mul_pow]
        unfold boundConstant
        change _ = (6*(N n:ℝ)*3^(N n-1))/(lowerConstant μ*κ^(n-1))*(d x)^(N n-n)
        field_simp [ne_of_gt (constants_positive μ).1,ne_of_gt hκ,ne_of_gt hx.2]
  · rw [weight,dite_eq_right hx]
    exact mul_nonneg (boundConstant_nonneg μ hκ.le) (pow_nonneg (d_nonneg x) _)

end HenonLaneEmden.AdaptiveCap
end
end AdaptiveCaps

end OAI
