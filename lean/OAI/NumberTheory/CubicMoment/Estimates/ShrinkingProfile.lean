import OAI.NumberTheory.CubicMoment.Estimates.NormProfileOperator

namespace OAI

/-! Polynomial seminorm costs for affine shrinking of a fixed cutoff. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

lemma iteratedFDeriv_comp_sub_real (f : ℝ → ℂ) (c : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => f (x-c)) = fun x => iteratedFDeriv ℝ n f (x-c) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    funext x
    simp only [iteratedFDeriv_succ_eq_comp_left,ih,Function.comp_apply,fderiv_comp_sub]

def affineSchwartzProfile (f : 𝓢(ℝ,ℂ)) (J c : ℝ) (hJ : J ≠ 0) : 𝓢(ℝ,ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ J hJ).toContinuousLinearEquiv f).compSubConstCLM ℂ c

@[simp] lemma affineSchwartzProfile_apply (f : 𝓢(ℝ,ℂ)) (J c : ℝ) (hJ : J ≠ 0) (x : ℝ) :
    affineSchwartzProfile f J c hJ x = f (J*(x-c)) := rfl

lemma affineSchwartzProfile_deriv_norm (f : 𝓢(ℝ,ℂ)) (J c : ℝ) (hJ : J ≠ 0)
    (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (affineSchwartzProfile f J c hJ) x‖ =
      |J|^n*‖iteratedFDeriv ℝ n f (J*(x-c))‖ := by
  have he : (affineSchwartzProfile f J c hJ : ℝ → ℂ) = fun x => (fun y => f (J • y)) (x-c) := rfl
  rw [he,iteratedFDeriv_comp_sub_real (fun y => f (J • y)) c n,
    iteratedFDeriv_comp_const_smul J (f.smooth n),
    norm_smul,Real.norm_eq_abs,abs_pow]
  rfl

theorem affineSchwartzProfile_seminorm (f : 𝓢(ℝ,ℂ)) {J c : ℝ}
    (hJ : 1 ≤ J) (hc : |c| ≤ 2) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (affineSchwartzProfile f J c (by linarith)) ≤
      6^k*J^n*((Finset.Iic (k,n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) f := by
  have hJ0 : 0 < J := by linarith
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  rw [affineSchwartzProfile_deriv_norm,abs_of_pos hJ0]
  have hx : ‖x‖ ≤ 3*(1+‖J*(x-c)‖) := by
    have htri := norm_add_le (x-c) c
    have hh : ‖x-c‖ ≤ J*‖x-c‖ := le_mul_of_one_le_left (_root_.norm_nonneg _) hJ
    rw [norm_mul,Real.norm_of_nonneg hJ0.le]
    rw [sub_add_cancel] at htri
    have hc' : ‖c‖ ≤ 2 := by simpa only [Real.norm_eq_abs] using hc
    nlinarith [_root_.norm_nonneg (x-c)]
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (k,n)) (k := k) (n := n) (le_refl _) (le_refl _) f (J*(x-c))
  calc
    _ ≤ (3*(1+‖J*(x-c)‖))^k*(J^n*‖iteratedFDeriv ℝ n f (J*(x-c))‖) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (_root_.norm_nonneg _) hx k) (by positivity)
    _ = (3^k*J^n)*((1+‖J*(x-c)‖)^k*‖iteratedFDeriv ℝ n f (J*(x-c))‖) := by
      rw [mul_pow]
      ring
    _ ≤ (3^k*J^n)*(2^k*((Finset.Iic (k,n)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) f) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [show (6:ℝ)^k = 3^k*2^k by rw [←mul_pow]; norm_num]; ring

/-- Every fixed finite family of seminorms has a polynomial shrinking cost. -/
theorem affineSchwartzProfile_finite_cost (f : 𝓢(ℝ,ℂ)) (I : Finset (ℕ × ℕ)) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧ ∀ (J c : ℝ) (hJ : 1 ≤ J), |c| ≤ 2 →
      (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
        (affineSchwartzProfile f J c (by linarith)) ≤ K*J^d := by
  classical
  let d := I.sup Prod.snd
  let a (m : ℕ × ℕ) := (6:ℝ)^m.1 *
    ((Finset.Iic m).sup (fun j => SchwartzMap.seminorm ℝ j.1 j.2)) f
  let K := 1+∑ m ∈ I, a m
  have ha (m : ℕ × ℕ) : 0 ≤ a m := by dsimp [a]; positivity
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun m (_ : m ∈ I) => ha m)
    dsimp [K]
    linarith
  refine ⟨d,K,hK,?_⟩
  intro J c hJ hc
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro m hm
  have hn : m.2 ≤ d := Finset.le_sup (f := Prod.snd) hm
  have hmK : a m ≤ K := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ I) => ha j) hm
    dsimp [K]
    linarith
  calc
    _ ≤ 6^m.1*J^m.2*((Finset.Iic m).sup
        (fun j => SchwartzMap.seminorm ℝ j.1 j.2)) f :=
      affineSchwartzProfile_seminorm f hJ hc m.1 m.2
    _ = a m*J^m.2 := by dsimp [a]; ring
    _ ≤ K*J^d := mul_le_mul hmK (pow_le_pow_right₀ hJ hn) (by positivity) hK.le

end CubicFirstMoment

end

end OAI
