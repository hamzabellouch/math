import Mathlib
import OAI.Probability.SKSupport.Foundations.ExpTranslateLocalBound

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

structure BoundedSmooth (g : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  bounds : ∀ n : ℕ, ∃ C : ℝ≥0, ∀ x, |iteratedDeriv n g x| ≤ C

lemma BoundedSmooth.bound {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    ∃ C : ℝ≥0, ∀ x, |g x| ≤ C := by simpa using hg.bounds 0

lemma BoundedSmooth.deriv {g : ℝ → ℝ} (hg : BoundedSmooth g) : BoundedSmooth (deriv g) := by
  constructor
  · exact contDiff_infty_iff_deriv.mp hg.smooth |>.2
  · intro n
    simpa only [iteratedDeriv_succ'] using hg.bounds (n+1)

lemma BoundedSmooth.const (c : ℝ) : BoundedSmooth (fun _ : ℝ => c) := by
  constructor
  · exact contDiff_const
  · intro n
    refine ⟨Real.nnabs c, fun x => ?_⟩
    cases n <;> simp [iteratedDeriv_const, Real.coe_nnabs]

lemma BoundedSmooth.add {f g : ℝ → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x+g x) := by
  constructor
  · exact hf.smooth.add hg.smooth
  · intro n
    obtain ⟨A,hA⟩ := hf.bounds n
    obtain ⟨B,hB⟩ := hg.bounds n
    refine ⟨A+B, fun x => ?_⟩
    rw [iteratedDeriv_fun_add (n := n) (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      (hg.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
    exact (abs_add_le _ _).trans (add_le_add (hA x) (hB x))

lemma BoundedSmooth.mul {f g : ℝ → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x*g x) := by
  classical
  constructor
  · exact hf.smooth.mul hg.smooth
  · intro n
    choose A hA using hf.bounds
    choose B hB using hg.bounds
    refine ⟨∑ i ∈ Finset.range (n+1), (n.choose i:ℝ≥0)*A i*B (n-i), fun x => ?_⟩
    rw [iteratedDeriv_fun_mul (n := n) (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      (hg.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    simp only [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (n.choose i:ℝ) from Nat.cast_nonneg _)]
    gcongr
    · exact hA i x
    · exact hB (n-i) x

lemma BoundedSmooth.const_mul {g : ℝ → ℝ} (hg : BoundedSmooth g) (c : ℝ) :
    BoundedSmooth (fun x => c*g x) := (BoundedSmooth.const c).mul hg

structure RegularDatum (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  deriv_bounded : BoundedSmooth (deriv f)

lemma weighted_derivative_boundedSmooth {f g : ℝ → ℝ}
    (hf : RegularDatum f) (hg : BoundedSmooth g) (c : ℝ) :
    BoundedSmooth (fun x => deriv g x+c*g x*deriv f x) :=
  hg.deriv.add ((hg.const_mul c).mul hf.deriv_bounded)

lemma weighted_derivative_formula {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    deriv (semigroup h (fun z => g z*Real.exp (c*f z))) =
      semigroup h (fun z => (deriv g z+c*g z*deriv f z)*Real.exp (c*f z)) := by
  obtain ⟨G,hG⟩ := hg.bound
  obtain ⟨G₁,hG₁⟩ := hg.deriv.bound
  funext x
  exact (hasDerivAt_semigroup_weight_exp (hf.smooth.of_le (by simp)) hLip
    (hg.smooth.of_le (by simp)) hG hG₁ hc h x).deriv

lemma contDiff_nat_semigroup_weight_exp {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (h : ℝ≥0) (n : ℕ) : ∀ g : ℝ → ℝ, BoundedSmooth g →
    ContDiff ℝ n (semigroup h (fun z => g z*Real.exp (c*f z))) := by
  induction n with
  | zero =>
      intro g hg
      rw [Nat.cast_zero, contDiff_zero]
      apply Differentiable.continuous (𝕜 := ℝ)
      intro x
      obtain ⟨G,hG⟩ := hg.bound
      obtain ⟨G₁,hG₁⟩ := hg.deriv.bound
      exact (hasDerivAt_semigroup_weight_exp (hf.smooth.of_le (by simp)) hLip
        (hg.smooth.of_le (by simp)) hG hG₁ hc h x).differentiableAt
  | succ n IH =>
      intro g hg
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨?_, by simp, ?_⟩
      · intro x
        obtain ⟨G,hG⟩ := hg.bound
        obtain ⟨G₁,hG₁⟩ := hg.deriv.bound
        exact (hasDerivAt_semigroup_weight_exp (hf.smooth.of_le (by simp)) hLip
          (hg.smooth.of_le (by simp)) hG hG₁ hc h x).differentiableAt
      · rw [weighted_derivative_formula hf hLip hg hc h]
        exact IH _ (weighted_derivative_boundedSmooth hf hg c)

lemma contDiff_semigroup_weight_exp {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    ContDiff ℝ ∞ (semigroup h (fun z => g z*Real.exp (c*f z))) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n hn
  exact contDiff_nat_semigroup_weight_exp hf hLip hc h n g hg

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
