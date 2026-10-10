import Mathlib
import OAI.Probability.SKSupport.Foundations.Finite

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure BoundedSmoothFamily (F : ℝ → ℝ → ℝ) : Prop where
  measurable : Measurable (fun p : ℝ × ℝ => F p.1 p.2)
  regular : ∀ t, BoundedSmooth (F t)
  bounds : ∀ n : ℕ, ∃ C : ℝ≥0, ∀ t x, |iteratedDeriv n (F t) x| ≤ C

lemma BoundedSmoothFamily.bound {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    ∃ C : ℝ≥0, ∀ t x, |F t x| ≤ C := by simpa using hF.bounds 0

lemma BoundedSmoothFamily.deriv {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    BoundedSmoothFamily (fun t => deriv (F t)) := by
  refine ⟨measurable_spatial_deriv hF.measurable
    (fun t => (hF.regular t).smooth.differentiable (by simp)),fun t => (hF.regular t).deriv,?_⟩
  intro n
  simpa only [iteratedDeriv_succ'] using hF.bounds (n+1)

lemma BoundedSmoothFamily.mul {F G : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hG : BoundedSmoothFamily G) :
    BoundedSmoothFamily (fun t x => F t x*G t x) := by
  classical
  refine ⟨hF.measurable.mul hG.measurable,fun t => (hF.regular t).mul (hG.regular t),?_⟩
  intro n
  choose A hA using hF.bounds
  choose B hB using hG.bounds
  refine ⟨∑ j ∈ Finset.range (n+1), (n.choose j:ℝ≥0)*A j*B (n-j),fun t x => ?_⟩
  rw [iteratedDeriv_fun_mul (n := n)
    ((hF.regular t).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    ((hG.regular t).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
  push_cast
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ (n.choose j:ℝ) from Nat.cast_nonneg _)]
  gcongr
  · exact hA j t x
  · exact hB (n-j) t x

lemma BoundedSmoothFamily.timeConst {d : ℝ → ℝ} {C : ℝ≥0}
    (hm : Measurable d) (hC : ∀ t, |d t| ≤ C) :
    BoundedSmoothFamily (fun t (_x : ℝ) => d t) := by
  refine ⟨hm.comp measurable_fst,fun t => BoundedSmooth.const (d t),?_⟩
  intro n
  cases n with
  | zero => exact ⟨C,fun t x => by simpa only [iteratedDeriv_zero] using hC t⟩
  | succ n => exact ⟨0,fun t x => by simp [iteratedDeriv_const]⟩

lemma BoundedSmoothFamily.iteratedDeriv {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (n : ℕ) :
    BoundedSmoothFamily (fun t => iteratedDeriv n (F t)) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma finiteGradient_family {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (fun t => deriv (finiteValue c h f N i t)) := by
  refine ⟨measurable_spatial_deriv (measurable_finiteValue hf hLip c h N i)
    (fun t => (finiteValue_regular hf hLip c h N i t).smooth.differentiable (by simp)),
    fun t => (finiteValue_regular hf hLip c h N i t).deriv_bounded,?_⟩
  intro n
  simpa only [iteratedDeriv_succ'] using finiteValue_uniform_derivative_bounds hf hLip c h N i n

lemma finiteCoeff_family (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (fun t (_x : ℝ) => finiteCoeff c h N i t) := by
  obtain ⟨C,hC⟩ := finiteCoeff_bounds c h N i
  exact BoundedSmoothFamily.timeConst (measurable_finiteCoeff c h N i)
    (fun t => by simpa only [abs_of_nonneg (hC t).1] using (hC t).2)

lemma finiteSource_family {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (finiteSource c h f N i) := by
  have hU := finiteGradient_family hf hLip c h N i
  change BoundedSmoothFamily (fun t x => finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) x)^2)
  simpa only [pow_two] using (finiteCoeff_family c h N i).mul (hU.mul hU)

def finiteBurgersSource (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) : ℝ :=
  finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) x*deriv (deriv (finiteValue c h f N i t)) x)

lemma finiteBurgersSource_family {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (finiteBurgersSource c h f N i) := by
  have hU := finiteGradient_family hf hLip c h N i
  exact (finiteCoeff_family c h N i).mul (hU.mul hU.deriv)

lemma deriv_finiteSource {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    deriv (finiteSource c h f N i t) = fun x => 2*finiteBurgersSource c h f N i t x := by
  funext x
  have hd := (((finiteValue_regular hf hLip c h N i t).deriv_bounded.smooth.differentiable (by simp) x).hasDerivAt.fun_pow 2).const_mul (finiteCoeff c h N i t)
  change deriv (fun x => finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) x)^2) x = _
  have hd' : deriv (fun z => finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) z)^2) x =
      finiteCoeff c h N i t*(2*deriv (finiteValue c h f N i t) x*deriv (deriv (finiteValue c h f N i t)) x) := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using hd.deriv
  rw [hd']
  simp only [finiteBurgersSource]
  ring

lemma finiteGradient_mild {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (N:ℝ)*h) (x : ℝ) :
    deriv (finiteValue c h f N i a) x = varianceHeat (b-a) (deriv (finiteValue c h f N i b)) x+
      ∫ r in a..b, varianceHeat (r-a) (finiteBurgersSource c h f N i r) x := by
  have hS := finiteSource_family hf hLip c h N i
  obtain ⟨A,hA⟩ := hS.bound
  obtain ⟨B,hB⟩ := hS.deriv.bound
  have hDt := hasDerivAt_integral_varianceHeat hS.measurable hS.regular hA hB a b x
  have hbreg := finiteValue_regular hf hLip c h N i b
  have hbLip := finiteValue_lipschitz hLip c h N i b
  have hHt : HasDerivAt (varianceHeat (b-a) (finiteValue c h f N i b))
      (varianceHeat (b-a) (deriv (finiteValue c h f N i b)) x) x :=
    hasDerivAt_scaled_space (hbreg.smooth.of_le (by simp)) (exponentialBound_of_lipschitz hbLip)
      (ExponentialBound.of_bounded (A := 1) (fun z => by
        simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀ := z) hbLip)) (Real.sqrt (b-a)) x
  have heFun : finiteValue c h f N i a = fun z =>
      varianceHeat (b-a) (finiteValue c h f N i b) z+
        (1/2)*(∫ r in a..b, varianceHeat (r-a) (finiteSource c h f N i r) z) :=
    funext (finiteValue_mild hf hLip c h N i ha hab hb)
  have hdR : deriv (fun z => varianceHeat (b-a) (finiteValue c h f N i b) z+
      (1/2)*(∫ r in a..b, varianceHeat (r-a) (finiteSource c h f N i r) z)) x =
      varianceHeat (b-a) (deriv (finiteValue c h f N i b)) x+
        (1/2)*(∫ r in a..b, varianceHeat (r-a) (deriv (finiteSource c h f N i r)) x) :=
    (hHt.add (hDt.const_mul (1/2))).deriv
  rw [heFun,hdR]
  simp_rw [deriv_finiteSource hf hLip,varianceHeat_const_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

end ZeroTemperatureSK.Heat

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

end
end
end
end
end

end OAI
