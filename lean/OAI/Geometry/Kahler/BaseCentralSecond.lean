import OAI.Geometry.Kahler.BaseDensityStep

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma expSum_hasDeriv (s : Finset ℤ) (a : ℤ → ℂ) (w : ℤ → ℝ) (z : ℂ) :
    HasDerivAt (expSum s a w) (expSum s (fun n => Complex.I*(w n:ℂ)*a n) w z) z := by
  have hh := HasDerivAt.sum (u := s) (fun n hn =>
    (((hasDerivAt_id z).const_mul (Complex.I*(w n:ℂ))).cexp).const_mul (a n))
  convert! hh using 1
  · ext t; simp [expSum,Finset.sum_apply]
  · unfold expSum
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [id]
    ring

lemma expSum_iteratedDeriv_two (s : Finset ℤ) (a : ℤ → ℂ) (w : ℤ → ℝ) :
    iteratedDeriv 2 (expSum s a w) 0 = ∑ n ∈ s, -(w n:ℂ)^2*a n := by
  have hd : deriv (expSum s a w)=expSum s (fun n => Complex.I*(w n:ℂ)*a n) w :=
    funext (fun z => (expSum_hasDeriv s a w z).deriv)
  rw [iteratedDeriv_succ,iteratedDeriv_one,hd,(expSum_hasDeriv _ _ _ _).deriv]
  unfold expSum
  simp only [mul_zero,Complex.exp_zero,mul_one]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = Complex.I^2*(w n:ℂ)^2*a n := by ring
    _ = _ := by rw [Complex.I_sq]; ring

lemma phase_second_weighted {W : Base → ℝ} (hW : ContDiff ℝ ∞ W)
    {ℓ : ℕ} (hband : PhaseBandwidth W ℓ) {q A : ℝ} (hq : 0 < q) (hA : 0 ≤ A)
    (hℓ : (ℓ:ℝ) ≤ 2*q) (N : ℕ) (ξ : Sphere)
    (hpos : ∀ z : Circle, 0 < W ((z:ℂ) • (ξ:Base)))
    (hg : ∀ u : ℝ, W ((Circle.exp u:ℂ) • (ξ:Base)) ≤ A*(1+q*|u|)^N*W ξ) :
    |phaseDerivative (phaseDerivative W) ξ| ≤ (2*A*4^N*Real.exp 2)*q^2*W ξ := by
  obtain ⟨s,a,hs,he⟩ := hband ξ
  let w : ℤ → ℝ := fun n => (n:ℝ)/q
  have hw : ∀ n ∈ s, |w n| ≤ 2 := by
    intro n hn
    rw [show w n=(n:ℝ)/q from rfl,abs_div,abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    have hn' : |(n:ℝ)| ≤ (ℓ:ℝ) := by exact_mod_cast hs n hn
    linarith
  have hfun : ∀ x : ℝ, expSum s a w x = (W ((Circle.exp (x/q):ℂ) • (ξ:Base)):ℂ) := by
    intro x
    rw [he]
    unfold expSum phaseSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [phaseChar_exp]
    congr 2
    dsimp [w]
    push_cast
    ring
  have hp : 0 < W ξ := by simpa using hpos 1
  have hb : ∀ x : ℝ, ‖expSum s a w x‖ ≤ (A*W ξ)*(1+|x|)^N := by
    intro x
    rw [hfun,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos (Circle.exp (x/q)))]
    have ht := hg (x/q)
    rw [abs_div,abs_of_pos hq,mul_div_cancel₀ _ hq.ne'] at ht
    nlinarith
  have hbd := expSum_second_derivative_bound s a w N hw (mul_nonneg hA hp.le) hb
  rw [expSum_iteratedDeriv_two] at hbd
  have hdiff := hW.differentiable (by simp)
  have hdiffT := (phaseDerivative_smooth hW).differentiable (by simp)
  have hT : ∀ z : Circle, (phaseDerivative W ((z:ℂ) • (ξ:Base)):ℂ) =
      phaseSum s (fun n => (n:ℂ)*Complex.I*a n) z := phaseDerivative_expansion hdiff ξ s a he
  have hTT := phaseDerivative_expansion hdiffT ξ s _ hT 1
  simp only [Circle.coe_one,one_smul,phaseSum,phaseChar_one,mul_one] at hTT
  have hsc : (phaseDerivative (phaseDerivative W) ξ:ℂ) =
      (q:ℂ)^2 * ∑ n ∈ s, -(w n:ℂ)^2*a n := by
    rw [hTT,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [w]
    push_cast
    have hq' : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    calc
      _ = Complex.I^2*(n:ℂ)^2*a n := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hh := congrArg norm hsc
  simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,norm_pow,abs_of_pos hq] at hh
  rw [hh]
  have ht := mul_le_mul_of_nonneg_left hbd (sq_nonneg q)
  nlinarith

end PinchedHartogs.BaseConstruction

end

end OAI
