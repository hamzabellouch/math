import Mathlib
import OAI.Probability.SKSupport.Control.ValueDifference

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

def OrderParameter.chord (γ β : OrderParameter) (ε : ℝ) (hε : ε ∈ Icc (0:ℝ) 1) : OrderParameter where
  val := fun t => (1-ε)*γ.val t+ε*β.val t
  nonneg := fun t => add_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) (γ.nonneg t)) (mul_nonneg hε.1 (β.nonneg t))
  monotone := fun a b hab => add_le_add (mul_le_mul_of_nonneg_left (γ.monotone hab) (sub_nonneg.mpr hε.2))
    (mul_le_mul_of_nonneg_left (β.monotone hab) hε.1)
  right_continuous := fun t => ((γ.right_continuous t).const_mul (1-ε)).add ((β.right_continuous t).const_mul ε)
  integrable := by
    have he : extend (fun t => (1-ε)*γ.val t+ε*β.val t)=fun t => (1-ε)*extend γ.val t+ε*extend β.val t := by
      funext t
      by_cases ht : t ∈ Ico (0:ℝ) 1 <;> simp [extend,ht]
    rw [he]
    exact (γ.integrable.const_mul (1-ε)).add (β.integrable.const_mul ε)

lemma OrderParameter.chord_extend (γ β : OrderParameter) (ε : ℝ) (hε : ε ∈ Icc (0:ℝ) 1) (t : ℝ) :
    extend (γ.chord β ε hε).val t=extend γ.val t+ε*(extend β.val t-extend γ.val t) := by
  by_cases ht : t ∈ Ico (0:ℝ) 1
  · simp only [extend,dite_eq_left ht,chord];ring
  · simp [extend,ht]

lemma OrderParameter.chord_distance (γ β : OrderParameter) (ε : ℝ) (hε : ε ∈ Icc (0:ℝ) 1) :
    coefficientDistance (γ.chord β ε hε) γ=ε*coefficientDistance β γ := by
  simp only [coefficientDistance,γ.chord_extend β ε hε,add_sub_cancel_left,abs_mul,abs_of_nonneg hε.1]
  rw [intervalIntegral.integral_const_mul]

lemma OrderParameter.chord_bound (γ β : OrderParameter) (ε : ℝ) (hε : ε ∈ Icc (0:ℝ) 1) (t : Time) :
    (γ.chord β ε hε).val t ≤ γ.val t+β.val t := by
  change (1-ε)*γ.val t+ε*β.val t ≤ _
  nlinarith [mul_nonneg hε.1 (γ.nonneg t),mul_nonneg (sub_nonneg.mpr hε.2) (β.nonneg t)]

def variationStep (n : ℕ) : ℝ := 1/((n:ℝ)+1)
lemma variationStep_pos (n : ℕ) : 0 < variationStep n := by unfold variationStep;positivity
lemma variationStep_mem (n : ℕ) : variationStep n ∈ Icc (0:ℝ) 1 := by
  refine ⟨(variationStep_pos n).le,?_⟩
  unfold variationStep
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
  norm_num
lemma variationStep_limit : Tendsto variationStep atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)
  simpa only [variationStep,one_div,Function.comp_def,Nat.cast_add,Nat.cast_one] using tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))

def perturbation (γ β : OrderParameter) (n : ℕ) : OrderParameter := γ.chord β (variationStep n) (variationStep_mem n)

lemma perturbation_diff (γ β : OrderParameter) (n : ℕ) (t : ℝ) :
    extend (perturbation γ β n).val t-extend γ.val t=variationStep n*(extend β.val t-extend γ.val t) := by
  simp only [perturbation,γ.chord_extend β _ _,add_sub_cancel_left]

lemma perturbation_distance_limit (γ β : OrderParameter) :
    Tendsto (fun n => coefficientDistance (perturbation γ β n) γ) atTop (𝓝 0) := by
  simp only [perturbation,OrderParameter.chord_distance]
  simpa only [zero_mul] using variationStep_limit.mul_const (coefficientDistance β γ)

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

lemma finiteCoeff_offset (c d : ℕ → ℝ≥0) (h : ℝ≥0) (ε : ℝ) (N i : ℕ)
    (he : ∀ j < N, (d (i+j):ℝ)=(c (i+j):ℝ)+ε)
    {t : ℝ} (ht : t ≤ (N:ℝ)*h) (hN : 0 < N) :
    finiteCoeff d h N i t=finiteCoeff c h N i t+ε := by
  induction N generalizing i t with
  | zero => omega
  | succ N ih =>
    by_cases hh : t ≤ h
    · simp only [finiteCoeff,ite_eq_left hh]
      simpa only [Nat.add_zero] using he 0 (by omega)
    · simp only [finiteCoeff,ite_eq_right hh]
      have hp : 0 < N := by
        by_contra hn
        have hn0 : N=0 := by omega
        subst N
        norm_num at ht
        exact hh ht
      apply ih (i+1) _ _ hp
      · intro j hj
        simpa only [show i+1+j=i+(j+1) by omega] using he (j+1) (by omega)
      · push_cast at ht
        nlinarith

def positiveCoeff (γ : OrderParameter) (n j : ℕ) : ℝ≥0 :=
  approxCoeff γ n (min j n)+approxMesh n

def positiveGamma (γ : OrderParameter) (n : ℕ) : ℝ → ℝ :=
  finiteCoeff (positiveCoeff γ n) (approxMesh n) (n+1) 0

def positiveTerminal (γ : OrderParameter) (n : ℕ) : ℝ :=
  ((n+1:ℕ):ℝ)+(positiveCoeff γ n n:ℝ)

lemma positiveCoeff_pos (γ : OrderParameter) (n j : ℕ) : 0 < (positiveCoeff γ n j:ℝ) := by
  unfold positiveCoeff
  exact_mod_cast add_pos_of_nonneg_of_pos (bot_le : 0 ≤ approxCoeff γ n (min j n)) (approxMesh_pos n)

lemma positiveCoeff_monotone (γ : OrderParameter) (n : ℕ) : Monotone (positiveCoeff γ n) := by
  intro i j hij
  unfold positiveCoeff
  apply add_le_add _ le_rfl
  apply NNReal.coe_le_coe.mp
  rw [approxCoeff_eq γ n _ (by omega),approxCoeff_eq γ n _ (by omega)]
  apply γ.monotone
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_min_right n hij) (approxMesh n).coe_nonneg

lemma positiveCoeff_bound (γ : OrderParameter) (n j : ℕ) : (positiveCoeff γ n j:ℝ) ≤ positiveTerminal γ n := by
  have he : positiveCoeff γ n j=positiveCoeff γ n (min j n) := by simp only [positiveCoeff,min_assoc,min_self]
  have hh := positiveCoeff_monotone γ n (min_le_right j n)
  rw [← he] at hh
  unfold positiveTerminal
  exact (show (positiveCoeff γ n j:ℝ) ≤ positiveCoeff γ n n from hh).trans (by linarith [Nat.cast_nonneg (α := ℝ) (n+1)])

lemma positiveTerminal_pos (γ : OrderParameter) (n : ℕ) : 0 < positiveTerminal γ n := by
  unfold positiveTerminal;positivity

lemma positiveGamma_eq (γ : OrderParameter) (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    positiveGamma γ n t=approxGamma γ n t+(approxMesh n:ℝ) := by
  apply finiteCoeff_offset _ _ _ _ (n+1) 0 _ (by simpa only [approxMesh_horizon] using ht) (by omega)
  intro j hj
  simp only [Nat.zero_add,positiveCoeff,min_eq_left (by omega : j ≤ n),NNReal.coe_add]

lemma positiveGamma_intervalIntegrable (γ : OrderParameter) (n : ℕ) :
    IntervalIntegrable (positiveGamma γ n) volume 0 1 := finiteCoeff_intervalIntegrable _ _ _ _ _ _

lemma positiveGamma_L1_bound (γ : OrderParameter) (n : ℕ) :
    (∫ t in (0:ℝ)..1, |positiveGamma γ n t-extend γ.val t|) ≤
      (∫ t in (0:ℝ)..1, |approxGamma γ n t-extend γ.val t|)+(approxMesh n:ℝ) := by
  have hf : IntervalIntegrable (fun t => |approxGamma γ n t-extend γ.val t|) volume 0 1 := ((finiteCoeff_intervalIntegrable (approxCoeff γ n) (approxMesh n) (n+1) 0 0 1).sub γ.integrable.intervalIntegrable).abs
  have hg := ((positiveGamma_intervalIntegrable γ n).sub γ.integrable.intervalIntegrable).abs
  calc
    _ ≤ ∫ t in (0:ℝ)..1, |approxGamma γ n t-extend γ.val t|+(approxMesh n:ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hg (hf.add intervalIntegrable_const)
      intro t ht
      rw [positiveGamma_eq γ n ht.2]
      have he : approxGamma γ n t+(approxMesh n:ℝ)-extend γ.val t=
        (approxGamma γ n t-extend γ.val t)+(approxMesh n:ℝ) := by ring
      rw [he]
      exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (approxMesh n).coe_nonneg])
    _ = _ := by rw [intervalIntegral.integral_add hf intervalIntegrable_const,intervalIntegral.integral_const];simp

lemma positiveGamma_L1 (γ : OrderParameter) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1, |positiveGamma γ n t-extend γ.val t|) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _))
    (positiveGamma_L1_bound γ)
  simpa only [zero_add] using (approxGamma_L1 γ).add approxMesh_limit

lemma positiveGamma_bound (γ : OrderParameter) (n : ℕ) (t : Time) :
    positiveGamma γ n t ≤ γ.val t+1 := by
  rw [positiveGamma_eq γ n t.property.2.le]
  have hm : (approxMesh n:ℝ) ≤ 1 := by
    unfold approxMesh
    simp only [NNReal.coe_inv,NNReal.coe_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  exact add_le_add (approxGamma_bounds γ n t).2 hm

lemma positiveTerminal_inv_tendsto (γ : OrderParameter) :
    Tendsto (fun n => (positiveTerminal γ n)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => inv_nonneg.mpr (positiveTerminal_pos γ n).le) (fun n => ?_) approxMesh_limit
  change (positiveTerminal γ n)⁻¹ ≤ (((n+1:ℕ):ℝ))⁻¹
  apply inv_anti₀ (by positivity)
  unfold positiveTerminal
  exact le_add_of_nonneg_right (positiveCoeff γ n n).coe_nonneg

end ZeroTemperatureSK

end
end

end OAI
