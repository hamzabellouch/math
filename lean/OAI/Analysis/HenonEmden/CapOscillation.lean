import OAI.Analysis.HenonEmden.AdaptiveCaps

namespace OAI

universe uE

section CapOscillation

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.AdaptiveCap
open Cutoff CapWeights
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def normalizedOscConstant : ℝ :=
  2/(lowerConstant μ/2^(Module.finrank ℝ E-1))+
    2*(2^(Module.finrank ℝ E)*upperConstant μ)/(lowerConstant μ/2^(Module.finrank ℝ E-1))^2

def oscillationConstant (κ : ℝ) : ℝ :=
  wDerivativeConstant (Module.finrank ℝ E)*2^(N (Module.finrank ℝ E)-2) /
      (lowerConstant μ*κ^(Module.finrank ℝ E-1)) +
  (6*(N (Module.finrank ℝ E):ℝ)*3^(N (Module.finrank ℝ E)-1))*
    2^(N (Module.finrank ℝ E)-1)*normalizedOscConstant μ*6/κ^(Module.finrank ℝ E)

omit [BorelSpace E] [Nontrivial E] in
lemma oscillationConstant_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ oscillationConstant μ κ := by
  obtain ⟨hc,hC⟩ := constants_positive μ
  have hd := (constants_nonneg (Module.finrank ℝ E)).2.2
  dsimp [oscillationConstant,normalizedOscConstant]
  positivity

lemma normalized_close_oscillation {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) (hd : 0 < d x)
    (hxy : dist x y ≤ d x/2) (hnx : 1/2 ≤ ‖x‖) (hny : 1/2 ≤ ‖y‖)
    (e : sphere (0:E) 1) :
    |normalized μ.toSphere (direction x hx) (κ*d x) e-
        normalized μ.toSphere (direction y hy) (κ*d y) e| ≤
      normalizedOscConstant μ*6*dist x y/(κ*d x)^(Module.finrank ℝ E) := by
  have hg := abs_le.mp (d_oscillation x y)
  have hcomp : d x/2 ≤ d y ∧ d y ≤ 2*d x := by constructor <;> linarith
  have hr := sphere_normalized_oscillation μ (mul_pos hκ hd)
    (l := κ*d x) (l' := κ*d y) (by nlinarith [mul_pos hκ hd])
    (by nlinarith [mul_le_mul_of_nonneg_left hcomp.1 hκ.le])
    (by nlinarith [mul_pos hκ hd])
    (by nlinarith [mul_le_mul_of_nonneg_left hcomp.2 hκ.le])
    ((mul_le_of_le_one_left (d_nonneg x) hκ1).trans (d_le_one x))
    ((mul_le_of_le_one_left (d_nonneg y) hκ1).trans (d_le_one y)) e
    (θ := direction x hx) (θ' := direction y hy)
  change _ ≤ normalizedOscConstant μ*(dist (direction x hx) (direction y hy)+2*|κ*d x-κ*d y|)/(κ*d x)^Module.finrank ℝ E at hr
  apply hr.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg (mul_pos hκ hd).le _)
  have hc : 0 ≤ normalizedOscConstant μ := by
    obtain ⟨hc,hC⟩ := constants_positive μ; unfold normalizedOscConstant; positivity
  have hdir : dist (direction x hx) (direction y hy) ≤ 4*dist x y := normalize_dist_le hnx hny
  have hrad : |κ*d x-κ*d y| ≤ dist x y := by
    rw [← mul_sub,abs_mul,abs_of_pos hκ]
    exact (mul_le_mul_of_nonneg_left (d_oscillation x y) hκ.le).trans
      (by nlinarith [dist_nonneg (x := x) (y := y)])
  nlinarith

lemma weight_close_oscillation {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {x y : E} (hd : 0 < d x) (hxy : dist x y ≤ d x/2) (e : sphere (0:E) 1) :
    |weight μ κ e x-weight μ κ e y| ≤
      oscillationConstant μ κ*(d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E-1)*dist x y := by
  let n := Module.finrank ℝ E
  have hn : 1 ≤ n := Module.finrank_pos
  have hc := constants_positive μ
  have hg := abs_le.mp (d_oscillation x y)
  have hdy : 0 < d y := by linarith
  have hdyU : d y ≤ 2*d x := by linarith
  have hdist : dist x y ≤ 1/2 := by linarith [d_le_one x]
  by_cases hboth : ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1
  · rw [weight_inner μ κ e hboth.1,weight_inner μ κ e hboth.2,sub_self,abs_zero]
    exact mul_nonneg (mul_nonneg (oscillationConstant_nonneg μ hκ.le) (pow_nonneg hd.le _)) dist_nonneg
  have hnxy : 1/2 ≤ ‖x‖ ∧ 1/2 ≤ ‖y‖ := by
    have hnorm : |‖x‖-‖y‖| ≤ dist x y := by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y
    have hh := abs_le.mp hnorm
    push Not at hboth
    by_cases hx : ‖x‖ ≤ 1
    · have hy := hboth hx; constructor <;> linarith
    · push Not at hx; constructor <;> linarith
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith [hnxy.1] : 0 < ‖x‖))
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith [hnxy.2] : 0 < ‖y‖))
  let cₓ := normalized μ.toSphere (direction x hx0) (κ*d x) e
  let cᵧ := normalized μ.toSphere (direction y hy0) (κ*d y) e
  have hcx : 0 ≤ cₓ := normalized_nonneg _ _ _ _
  have hcy : 0 ≤ cᵧ := normalized_nonneg _ _ _ _
  have hcl : cₓ ≤ 1/(lowerConstant μ*(κ*d x)^(n-1)) := by
    exact (normalized_le_inv μ.toSphere _ (mul_pos hκ hd) e).trans (by
      simpa only [one_div] using one_div_le_one_div_of_le
        (mul_pos hc.1 (pow_pos (mul_pos hκ hd) _))
        (sphere_normalizer_bounds μ (direction x hx0) (mul_pos hκ hd)
          ((mul_le_of_le_one_left (d_nonneg x) hκ1).trans (d_le_one x))).1)
  have hco := normalized_close_oscillation μ hκ hκ1 hx0 hy0 hd hxy hnxy.1 hnxy.2 e
  have hwo : |w n x-w n y| ≤ wDerivativeConstant n*(2*d x)^(N n-2)*dist x y := by
    rw [abs_sub_comm]
    exact w_oscillation hn (by positivity) (by linarith)
  have hwy : w n y ≤ (6*(N n:ℝ)*3^(N n-1))*(2*d x)^(N n-1) := by
    rw [w_eq_profile]
    exact (wProfile_bound n (norm_nonneg y)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (d_nonneg y) hdyU _) (by positivity))
  rw [weight,dite_eq_left ⟨hx0,hd⟩,weight,dite_eq_left ⟨hy0,hdy⟩]
  change |w n x*cₓ-w n y*cᵧ| ≤ _
  calc
    _ ≤ |w n x-w n y| *cₓ+w n y*|cₓ-cᵧ| := by
      rw [show w n x*cₓ-w n y*cᵧ = (w n x-w n y)*cₓ+w n y*(cₓ-cᵧ) by ring]
      simpa only [abs_mul,abs_of_nonneg hcx,abs_of_nonneg (w_nonneg n y)] using abs_add_le ((w n x-w n y)*cₓ) (w n y*(cₓ-cᵧ))
    _ ≤ (wDerivativeConstant n*(2*d x)^(N n-2)*dist x y)*
        (1/(lowerConstant μ*(κ*d x)^(n-1))) +
        ((6*(N n:ℝ)*3^(N n-1))*(2*d x)^(N n-1))*
          (normalizedOscConstant μ*6*dist x y/(κ*d x)^n) := by
      apply add_le_add
      · exact mul_le_mul hwo hcl hcx (by have hh := (constants_nonneg n).2.2; positivity)
      · exact mul_le_mul hwy hco (abs_nonneg _) (by positivity)
    _ = _ := by
      have hN2 : N n-2 = (n-1)+(N n-n-1) := by dsimp [N]; omega
      have hN1 : N n-1 = n+(N n-n-1) := by dsimp [N]; omega
      have hd2 : (d x)^(N n-2) = (d x)^(n-1)*(d x)^(N n-n-1) := by rw [hN2,pow_add]
      have hd1 : (d x)^(N n-1) = (d x)^n*(d x)^(N n-n-1) := by rw [hN1,pow_add]
      simp only [mul_pow]
      rw [hd2,hd1]
      unfold oscillationConstant
      change _ = (wDerivativeConstant n*2^(N n-2)/(lowerConstant μ*κ^(n-1))+
        (6*(N n:ℝ)*3^(N n-1))*2^(N n-1)*normalizedOscConstant μ*6/κ^n)*(d x)^(N n-n-1)*dist x y
      field_simp [ne_of_gt hc.1,ne_of_gt hκ,ne_of_gt hd]

end HenonLaneEmden.AdaptiveCap
end
end CapOscillation

end OAI
