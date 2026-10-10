import Mathlib

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue

lemma second_order_remainder {f : ℝ → ℝ} {C : ℝ} (hf : ContDiff ℝ 2 f) (hC : 0 ≤ C)
    (hb : ∀ x, |deriv (deriv f) x| ≤ C) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d| ≤ (C/2)*d^2 := by
  by_cases hd : d=0
  · rw [hd, add_zero, mul_zero, sub_self, sub_zero, abs_zero]
    exact mul_nonneg (div_nonneg hC (by norm_num)) (sq_nonneg 0)
  have hne : x≠x+d := by intro hx; apply hd; linarith
  have h1 : iteratedDerivWithin 1 f (uIcc x (x+d)) x=deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.of_le (by norm_num)).contDiffAt left_mem_uIcc,iteratedDeriv_one]
  have ht : taylorWithinEval f 1 (uIcc x (x+d)) x (x+d)=f x+deriv f x*d := by
    rw [taylorWithinEval_succ,taylor_within_zero_eval,h1]
    norm_num
    ring
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hf.contDiffOn
  rw [ht] at hy
  have he : f (x+d)-f x-deriv f x*d=deriv (deriv f) y*d^2/2 := by
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      mul_one,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] at hy
    convert hy using 1 <;> ring
  rw [he,abs_div,abs_mul,abs_of_nonneg (sq_nonneg d)]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right (hb y) (sq_nonneg d)]

lemma derivative_difference_of_values {f g : ℝ → ℝ} {C ε d : ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hC : 0 ≤ C) (hd : 0<d)
    (hfb : ∀ x, |deriv (deriv f) x| ≤ C) (hgb : ∀ x, |deriv (deriv g) x| ≤ C)
    (he : ∀ x, |f x-g x|<ε) (x : ℝ) :
    |deriv f x-deriv g x| * d < 2*ε+C*d^2 := by
  have hf' := second_order_remainder hf hC hfb x d
  have hg' := second_order_remainder hg hC hgb x d
  have hid : (deriv f x-deriv g x)*d=
      (f (x+d)-g (x+d))-(f x-g x)-
        (f (x+d)-f x-deriv f x*d)+(g (x+d)-g x-deriv g x*d) := by ring
  have hmul : |deriv f x-deriv g x| * d = |(deriv f x-deriv g x)*d| := by rw [abs_mul,abs_of_pos hd]
  rw [hmul,hid]
  have hp := abs_sub (f (x+d)-g (x+d)) (f x-g x)
  have hq := abs_sub ((f (x+d)-g (x+d))-(f x-g x)) (f (x+d)-f x-deriv f x*d)
  have hb := abs_add_le ((f (x+d)-g (x+d))-(f x-g x)-(f (x+d)-f x-deriv f x*d))
    (g (x+d)-g x-deriv g x*d)
  have h1 := he (x+d)
  have h2 := he x
  nlinarith

lemma uniform_derivative_limit {A : Type*} {F : ℕ → A → ℝ → ℝ} {f : A → ℝ → ℝ} {C : ℝ}
    (hF : TendstoUniformly (fun n (p : A×ℝ) ↦ F n p.1 p.2) (fun p ↦ f p.1 p.2) atTop)
    (hs : ∀ n a, ContDiff ℝ 2 (F n a)) (hC : 0 ≤ C)
    (hb : ∀ n a x, |deriv (deriv (F n a)) x| ≤ C) :
    TendstoUniformly (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2)
      (fun p ↦ deriv (f p.1) p.2) atTop ∧ ∀ a, Differentiable ℝ (f a) := by
  have hc : UniformCauchySeqOn (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2) atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let d := ε/(2*(C+1))
    have hd : 0<d := by dsimp [d]; positivity
    have hdC : C*d<ε/2 := by
      dsimp [d]
      have hn : 0<2*(C+1) := by positivity
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hn).mpr
      nlinarith
    have hcF := (hF.tendstoUniformlyOn (s := univ)).uniformCauchySeqOn
    obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp hcF (ε*d/4) (by positivity)
    refine ⟨N,?_⟩
    intro m hm n hn p hp
    have he : ∀ x, |F m p.1 x-F n p.1 x|<ε*d/4 := by
      intro x
      simpa only [Real.dist_eq] using hN m hm n hn (p.1,x) (mem_univ _)
    have hv := derivative_difference_of_values (hs m p.1) (hs n p.1) hC hd
      (hb m p.1) (hb n p.1) he p.2
    rw [Real.dist_eq]
    have hh : |deriv (F m p.1) p.2-deriv (F n p.1) p.2| * d<ε*d := by
      nlinarith [mul_lt_mul_of_pos_right hdC hd]
    nlinarith
  have hex (p : A×ℝ) : ∃ g : ℝ, Tendsto (fun n ↦ deriv (F n p.1) p.2) atTop (𝓝 g) :=
    cauchySeq_tendsto_of_complete (hc.cauchySeq (mem_univ p))
  choose g hg using hex
  have hG : TendstoUniformly (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2) g atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hc.tendstoUniformlyOn_of_tendsto (fun p _ ↦ hg p)
  have hgder (a : A) (x : ℝ) : HasDerivAt (f a) (g (a,x)) x := by
    apply hasDerivAt_of_tendstoUniformly (hG.comp (fun z ↦ (a,z)))
    · exact Eventually.of_forall (fun n y ↦ ((hs n a).differentiable (by norm_num) y).hasDerivAt)
    · intro y
      exact hF.tendsto_at (a,y)
  have heq : g=(fun p ↦ deriv (f p.1) p.2) := by
    funext p
    exact (hgder p.1 p.2).deriv.symm
  exact ⟨heq ▸ hG,fun a x ↦ (hgder a x).differentiableAt⟩

lemma contDiff_infty_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k hk =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp hk).2

lemma uniform_all_derivative_limits {A : Type*} {F : ℕ → A → ℝ → ℝ} {f : A → ℝ → ℝ}
    (hF : TendstoUniformly (fun n (p : A×ℝ) ↦ F n p.1 p.2) (fun p ↦ f p.1 p.2) atTop)
    (hs : ∀ n a, ContDiff ℝ ∞ (F n a))
    (hb : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ n a x, |iteratedDeriv (k+1) (F n a) x| ≤ C) :
    (∀ k, TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
      (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop) ∧ ∀ a, ContDiff ℝ ∞ (f a) := by
  have step (k : ℕ)
      (hk : TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
        (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop) :
      TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv (k+1) (F n p.1) p.2)
        (fun p ↦ iteratedDeriv (k+1) (f p.1) p.2) atTop ∧
        ∀ a, Differentiable ℝ (iteratedDeriv k (f a)) := by
    obtain ⟨C,hC,hbc⟩ := hb (k+1)
    have hh := uniform_derivative_limit (F := fun n a ↦ iteratedDeriv k (F n a))
      (f := fun a ↦ iteratedDeriv k (f a)) hk
      (fun n a ↦ (contDiff_infty_iteratedDeriv (hs n a) k).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hC (fun n a x ↦ by
          simpa only [iteratedDeriv_succ] using hbc n a x)
    simpa only [iteratedDeriv_succ] using hh
  have hc : ∀ k, TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
      (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hF
    | succ k hk => exact (step k hk).1
  refine ⟨hc,?_⟩
  intro a
  apply contDiff_iff_iteratedDeriv.mpr
  constructor
  · intro m hm
    exact ((step m (hc m)).2 a).continuous
  · intro m hm
    exact (step m (hc m)).2 a

end SKValue

end

end OAI
