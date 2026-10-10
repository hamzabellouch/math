import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApprox

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X]
lemma slopeApprox_antitone (f : X → ℝ) (x : X) : Antitone (fun n => slopeApprox f n x) := by
  intro i j hij
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hrad : (1 : ℝ) / (j+1) ≤ 1/(i+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  exact le_iSup_of_le y (le_iSup_of_le (hy.trans_le hrad) le_rfl)

lemma slopeApprox_const_mul (c : ℝ) (f : X → ℝ) (n : ℕ) (x : X) :
    slopeApprox (fun y => c * f y) n x = ENNReal.ofReal |c| * slopeApprox f n x := by
  unfold slopeApprox
  simp only [← mul_sub, abs_mul, mul_div_assoc, ENNReal.ofReal_mul (abs_nonneg c)]
  rw [ENNReal.mul_iSup]
  congr 1
  funext y
  rw [ENNReal.mul_iSup]

lemma localSlope_const_mul (c : ℝ) (f : X → ℝ) (x : X) :
    localSlope (fun y => c * f y) x = ENNReal.ofReal |c| * localSlope f x := by
  simp only [localSlope_eq_iInf_slopeApprox, slopeApprox_const_mul]
  exact (ENNReal.mul_iInf (fun h => (ENNReal.ofReal_ne_top h).elim)).symm

lemma localSlope_zero (x : X) : localSlope (fun _ : X => (0:ℝ)) x = 0 := by
  simpa only [zero_mul, abs_zero, ENNReal.ofReal_zero, Pi.zero_apply] using
    localSlope_const_mul 0 (fun _ : X => (0:ℝ)) x

lemma slopeApprox_add_le (f g : X → ℝ) (n : ℕ) (x : X) :
    slopeApprox (fun y => f y + g y) n x ≤ slopeApprox f n x + slopeApprox g n x := by
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hreal : |f y + g y - (f x + g x)| / dist y x ≤
      |f y - f x| / dist y x + |g y - g x| / dist y x := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ dist_nonneg
    convert abs_add_le (f y - f x) (g y - g x) using 1
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (|f y-f x| / dist y x + |g y-g x| / dist y x) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (|f y-f x| / dist y x) +
        ENNReal.ofReal (|g y-g x| / dist y x) := ENNReal.ofReal_add (by positivity) (by positivity)
    _ ≤ _ := by
      apply add_le_add
      · exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)
      · exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)

lemma localSlope_add_le (f g : X → ℝ) (x : X) :
    localSlope (fun y => f y + g y) x ≤ localSlope f x + localSlope g x := by
  simp only [localSlope_eq_iInf_slopeApprox]
  rw [ENNReal.iInf_add_iInf (fun i j => ⟨max i j, add_le_add
    (slopeApprox_antitone f x (le_max_left i j))
    (slopeApprox_antitone g x (le_max_right i j))⟩)]
  exact iInf_mono fun n => slopeApprox_add_le f g n x

variable [MeasurableSpace X] {m : Measure X}
lemma slope_energy_const_mul (c : ℝ) (f : X → ℝ) :
    (2:ℝ≥0∞)⁻¹ * (∫⁻ x, localSlope (fun y => c * f y) x ^ 2 ∂m) =
      ENNReal.ofReal (c^2) * ((2:ℝ≥0∞)⁻¹ * (∫⁻ x, localSlope f x ^ 2 ∂m)) := by
  simp_rw [localSlope_const_mul, mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  have hc : (ENNReal.ofReal |c|)^2 = ENNReal.ofReal (c^2) := by
    rw [← ENNReal.ofReal_pow (abs_nonneg c), sq_abs]
  rw [hc]
  ac_rfl

end WeakHessian

open Set
open scoped NNReal


namespace WeakHessian
variable {X : Type*} [PseudoMetricSpace X]

lemma lipschitz_exp_bounded {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    {B : ℝ} (hB : ∀ x, V x ≤ B) :
    LipschitzWith (⟨Real.exp B,(Real.exp_pos B).le⟩*L) (fun x => Real.exp (V x)) := by
  have he : LipschitzOnWith ⟨Real.exp B,(Real.exp_pos B).le⟩ Real.exp (Iic B) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => Real.differentiableAt_exp) _ (convex_Iic B)
    intro x hx
    change ‖deriv Real.exp x‖ ≤ Real.exp B
    simpa only [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr hx
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (he.dist_le_mul (V x) (hB x) (V y) (hB y)).trans (by
    change Real.exp B * dist (V x) (V y) ≤ (Real.exp B * (L:ℝ))*dist x y
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hV.dist_le_mul x y) (Real.exp_pos B).le)

lemma lipschitz_mul_bounded {f g : X → ℝ} {L T : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith T g)
    {A B : ℝ} (hA : ∀ x, |f x| ≤ A) (hB : ∀ x, |g x| ≤ B) :
    LipschitzWith (L*‖B‖₊+‖A‖₊*T) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_add,NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,Real.dist_eq]
  have hL := hf.dist_le_mul x y
  have hT := hg.dist_le_mul x y
  rw [Real.dist_eq] at hL hT
  calc
    |f x*g x-f y*g y| = |(f x-f y)*g x+f y*(g x-g y)| := by congr 1; ring
    _ ≤ |f x-f y| * |g x|+|f y| * |g x-g y| := by simpa only [abs_mul] using abs_add_le ((f x-f y)*g x) (f y*(g x-g y))
    _ ≤ ((L:ℝ)*dist x y)* |B|+|A| * ((T:ℝ)*dist x y) := by
      exact add_le_add
        (mul_le_mul hL ((hB x).trans (le_abs_self B)) (abs_nonneg _)
          (mul_nonneg L.coe_nonneg dist_nonneg))
        (mul_le_mul ((hA y).trans (le_abs_self A)) hT (abs_nonneg _) (abs_nonneg _))
    _ = ((L:ℝ)* |B|+|A| * (T:ℝ))*dist x y := by ring
lemma lipschitz_const_mul_real {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (c : ℝ) :
    LipschitzWith (‖c‖₊*L) (fun x => c*f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs]
  rw [← mul_sub,abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg _)

end WeakHessian

end

end OAI
