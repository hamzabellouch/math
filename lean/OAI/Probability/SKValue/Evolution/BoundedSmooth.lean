import Mathlib
import OAI.Probability.SKValue.Evolution.ColeHopfPDE

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

structure BoundedSmooth (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  bound : ∀ n : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ x, |iteratedDeriv n f x|≤C

lemma BoundedSmooth.bound_zero {f : ℝ → ℝ} (hf : BoundedSmooth f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, |f x|≤C := by
  simpa only [iteratedDeriv_zero] using hf.bound 0

lemma BoundedSmooth.const (c : ℝ) : BoundedSmooth (fun _ : ℝ ↦ c) := by
  refine ⟨contDiff_const,fun n ↦ ⟨|c|,abs_nonneg c,?_⟩⟩
  intro x
  by_cases hn : n=0
  · subst n; simp only [iteratedDeriv_zero,le_refl]
  · simp only [iteratedDeriv_const,ite_eq_right hn,abs_zero,abs_nonneg]

lemma BoundedSmooth.deriv {f : ℝ → ℝ} (hf : BoundedSmooth f) :
    BoundedSmooth (deriv f) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hf.smooth).2,?_⟩
  intro n
  simpa only [iteratedDeriv_succ'] using hf.bound (n+1)

lemma BoundedSmooth.add {f g : ℝ → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x ↦ f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,?_⟩
  intro n
  obtain ⟨A,hA,hfA⟩ := hf.bound n
  obtain ⟨B,hB,hgB⟩ := hg.bound n
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro x
  rw [iteratedDeriv_fun_add
    (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
    (hg.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
  exact (abs_add_le _ _).trans (add_le_add (hfA x) (hgB x))

lemma BoundedSmooth.mul {f g : ℝ → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x ↦ f x*g x) := by
  classical
  choose A hA hfA using hf.bound
  choose B hB hgB using hg.bound
  refine ⟨hf.smooth.mul hg.smooth,?_⟩
  intro n
  refine ⟨∑ i∈Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i),?_,?_⟩
  · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))
  · intro x
    rw [iteratedDeriv_fun_mul
      (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
      (hg.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hfA i x) (Nat.cast_nonneg _)) (hgB (n-i) x)
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))

lemma BoundedSmooth.const_mul {f : ℝ → ℝ} (hf : BoundedSmooth f) (c : ℝ) :
    BoundedSmooth (fun x ↦ c*f x) := (BoundedSmooth.const c).mul hf

lemma BoundedSmooth.expGrowth {f : ℝ → ℝ} (hf : BoundedSmooth f) :
    ExpGrowth f := by
  obtain ⟨C,hC,hfC⟩ := hf.bound_zero
  exact ExpGrowth.of_bound hC hfC

noncomputable def expJet (c : ℝ) (ψ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ ↦ 1
  | n+1 => fun x ↦ deriv (expJet c ψ n) x+expJet c ψ n x*(c*deriv ψ x)

lemma expJet_boundedSmooth {ψ : ℝ → ℝ} (hψ : BoundedSmooth (deriv ψ)) (c : ℝ) (n : ℕ) :
    BoundedSmooth (expJet c ψ n) := by
  induction n with
  | zero => exact BoundedSmooth.const 1
  | succ n ih => exact ih.deriv.add (ih.mul (hψ.const_mul c))

lemma exp_iteratedDeriv {ψ : ℝ → ℝ} (hψs : ContDiff ℝ ∞ ψ)
    (hψ : BoundedSmooth (deriv ψ)) (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)) =
      fun x ↦ Real.exp (c*ψ x)*expJet c ψ n x := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,expJet,mul_one]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hψd := hψs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))
    have hJd := (expJet_boundedSmooth hψ c n).smooth.differentiable
      (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))
    have hd := (((hψd x).hasDerivAt.const_mul c).exp).mul (hJd x).hasDerivAt
    convert! hd.deriv using 1
    dsimp only [expJet]
    ring

lemma exp_iteratedDeriv_growth {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0≤c) (n : ℕ) :
    ExpGrowth (iteratedDeriv n (fun x ↦ Real.exp (c*ψ x))) := by
  rw [exp_iteratedDeriv hψs hψ c n]
  obtain ⟨C,hC,hJ⟩ := (expJet_boundedSmooth hψ c n).bound_zero
  exact (ExpGrowth.exp_lipschitz hψl hc).mul_bounded hC hJ

lemma coleHopf_contDiff_of_pos {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0<c) (h : ℝ) :
    ContDiff ℝ ∞ (coleHopf c h ψ) := by
  have he : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  have hH := heat_contDiff he (exp_iteratedDeriv_growth hψl hψs hψ hc.le) h
  have hp (x : ℝ) : heat h (fun y ↦ Real.exp (c*ψ y)) x ≠0 :=
    (lipschitz_exp_integral_pos hψl hc.le x (Real.sqrt h)).ne'
  have heq : coleHopf c h ψ = fun x ↦ Real.log (heat h (fun y ↦ Real.exp (c*ψ y)) x)/c := by
    funext x
    simp only [coleHopf,ite_eq_right hc.ne']
  rw [heq]
  exact (hH.log hp).div_const c

end SKValue

end

end OAI
