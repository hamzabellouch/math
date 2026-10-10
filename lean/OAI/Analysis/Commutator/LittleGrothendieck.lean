import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter Set

namespace Kadison.LittleGrothendieck

lemma second_deriv_nonpos {f : ℝ → ℝ} {t d : ℝ}
    (hm : IsLocalMax f t) (hc : ContinuousAt f t)
    (h : HasDerivAt (deriv f) d t) : d ≤ 0 := by
  by_contra! hd
  have hmin := isLocalMin_of_deriv_deriv_pos (by rwa [h.deriv]) hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] fun _ => f t := by
    filter_upwards [hm,hmin] with x hx hy
    exact le_antisymm hx hy
  have hz := heq.deriv.deriv_eq
  rw [h.deriv, deriv_const', deriv_const] at hz
  exact (ne_of_gt hd) hz

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem selfAdjoint_square_at_unitary_max
    (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖ ≤ ‖T (u:A)‖)
    (a : A) (ha : IsSelfAdjoint a) :
    ‖T ((u:A)*a)‖^2 ≤ (inner ℂ (T (u:A)) (T ((u:A)*(a*a)))).re := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let b : A := Complex.I • a
  let c : ℝ → A := fun t => (u:A)*NormedSpace.exp (t • b)
  have hc (t : ℝ) : HasDerivAt c (c t*b) t := by
    simpa only [c, mul_assoc] using (hasDerivAt_exp_smul_const b t).const_mul (u:A)
  let v : ℝ → E := fun t => T (c t)
  let v' : ℝ → E := fun t => T (c t*b)
  have hv (t : ℝ) : HasDerivAt v (v' t) t := by
    exact (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hc t)
  have hv' (t : ℝ) : HasDerivAt v' (T (c t*b*b)) t := by
    exact (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t ((hc t).mul_const b)
  let f : ℝ → ℝ := fun t => ‖v t‖^2
  have hf (t : ℝ) : HasDerivAt f (2*(inner ℂ (v t) (v' t)).re) t := by
    simpa only [f, real_inner_eq_re_inner ℂ, ← RCLike.re_to_complex] using (hv t).norm_sq
  have hfun : deriv f=fun t => 2*(inner ℂ (v t) (v' t)).re := by
    funext t
    exact (hf t).deriv
  have hsecond : HasDerivAt (deriv f)
      (2*((inner ℂ (v' 0) (v' 0)).re+
          (inner ℂ (v 0) (T (c 0*b*b))).re)) 0 := by
    rw [hfun]
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.add_re, add_comm] using
      ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
        ((hv 0).inner ℂ (hv' 0))).const_mul 2)
  have hmax : IsLocalMax f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have ht : NormedSpace.exp (t • b) ∈ unitary A := by
      change NormedSpace.exp (t • (Complex.I • a)) ∈ unitary A
      have hs : IsSelfAdjoint (t • a) := (IsSelfAdjoint.all t).smul ha
      rw [smul_comm t Complex.I a]
      exact (selfAdjoint.expUnitary (⟨t • a,hs⟩ : selfAdjoint A)).property
    have hh := hu (u*⟨NormedSpace.exp (t • b),ht⟩)
    apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa only [f,v,c,zero_smul,NormedSpace.exp_zero,mul_one,Submonoid.coe_mul] using hh
  have hs := second_deriv_nonpos hmax (hf 0).continuousAt hsecond
  have hzero : c 0=(u:A) := by simp [c]
  have hbb : b*b=-(a*a) := by
    simp only [b,smul_mul_assoc,mul_smul_comm,smul_smul,Complex.I_mul_I,neg_one_smul]
  have hb2 : c 0*b*b=-((u:A)*(a*a)) := by rw [hzero,mul_assoc,hbb,mul_neg]
  have hvzero : v 0=T (u:A) := by simp only [v,hzero]
  have hv'zero : v' 0=Complex.I • T ((u:A)*a) := by
    simp only [v',hzero,b,mul_smul_comm,map_smul]
  rw [hvzero,hv'zero,hb2,map_neg,inner_neg_right,Complex.neg_re] at hs
  have hi : (inner ℂ (Complex.I • T ((u:A)*a)) (Complex.I • T ((u:A)*a))).re =
      ‖T ((u:A)*a)‖^2 := by simp [norm_smul, ← Complex.ofReal_pow]
  rw [hi] at hs
  linarith

theorem square_at_unitary_max
    (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖ ≤ ‖T (u:A)‖) (a : A) :
    ‖T ((u:A)*a)‖^2 ≤
      (inner ℂ (T (u:A)) (T ((u:A)*(star a*a+a*star a)))).re := by
  let h : A := realPart a
  let k : A := imaginaryPart a
  have hh := selfAdjoint_square_at_unitary_max T u hu h (realPart a).property
  have hk := selfAdjoint_square_at_unitary_max T u hu k (imaginaryPart a).property
  have hsplit : T ((u:A)*a)=T ((u:A)*h)+Complex.I • T ((u:A)*k) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
    simp only [mul_add, mul_smul_comm, map_add, map_smul, h, k]
  have hn : ‖T ((u:A)*a)‖ ≤ ‖T ((u:A)*h)‖+‖T ((u:A)*k)‖ := by
    rw [hsplit]
    simpa only [norm_smul, Complex.norm_I, one_mul] using
      norm_add_le (T ((u:A)*h)) (Complex.I • T ((u:A)*k))
  have hs : ‖T ((u:A)*a)‖^2 ≤ 2*(‖T ((u:A)*h)‖^2+‖T ((u:A)*k)‖^2) := by
    nlinarith [norm_nonneg (T ((u:A)*h)), norm_nonneg (T ((u:A)*k)),
      norm_nonneg (T ((u:A)*a)), sq_nonneg (‖T ((u:A)*h)‖-‖T ((u:A)*k)‖)]
  have heq : (inner ℂ (T (u:A)) (T ((u:A)*(star a*a+a*star a)))).re =
      2*((inner ℂ (T (u:A)) (T ((u:A)*(h*h)))).re+
         (inner ℂ (T (u:A)) (T ((u:A)*(k*k)))).re) := by
    rw [star_mul_self_add_self_mul_star]
    simp only [two_smul, mul_add, map_add, inner_add_right, Complex.add_re, h, k]
    ring
  rw [heq]
  linarith

theorem sum_sq_le_at_unitary_max {ι : Type*} [Fintype ι]
    (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖ ≤ ‖T (u:A)‖) (a : ι → A) :
    ∑ i, ‖T (a i)‖^2 ≤ ‖T‖^2 * (‖∑ i, star (a i)*a i‖+‖∑ i, a i*star (a i)‖) := by
  classical
  let b : ι → A := fun i => (star u:A)*a i
  have hb (i : ι) : (u:A)*b i=a i := by
    simp only [b, ← mul_assoc, Unitary.mul_star_self_of_mem u.property, one_mul]
  have hpoint (i : ι) := square_at_unitary_max T u hu (b i)
  simp only [hb] at hpoint
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hinner : (∑ i, (inner ℂ (T (u:A))
      (T ((u:A)*(star (b i)*b i+b i*star (b i))))).re) =
      (inner ℂ (T (u:A)) (T ((u:A)*∑ i, (star (b i)*b i+b i*star (b i))))).re := by
    simp only [Finset.mul_sum, map_sum, inner_sum, Complex.re_sum]
  rw [hinner] at hsum
  have hub : ‖T (u:A)‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖T‖*‖(u:A)‖ := T.le_opNorm _
      _ ≤ ‖T‖*1 := mul_le_mul_of_nonneg_left (by
        cases subsingleton_or_nontrivial A with
        | inl h => simpa only [Subsingleton.elim (u:A) 0, norm_zero] using (zero_le_one : (0:ℝ)≤1)
        | inr h => exact le_of_eq (CStarRing.norm_coe_unitary u)) (norm_nonneg _)
      _ = _ := mul_one _
  have hc : ‖∑ i, star (b i)*b i‖ = ‖∑ i, star (a i)*a i‖ := by
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [b, star_mul, star_star, mul_assoc]
    rw [← mul_assoc (u:A), Unitary.mul_star_self_of_mem u.property, one_mul]
  have hr : ‖∑ i, b i*star (b i)‖ = ‖∑ i, a i*star (a i)‖ := by
    have heq : (∑ i, b i*star (b i))=(star u:A)*(∑ i, a i*star (a i))*(u:A) := by
      simp only [Finset.mul_sum, Finset.sum_mul, b, star_mul, star_star, mul_assoc]
    rw [heq, CStarRing.norm_mul_coe_unitary]
    exact CStarRing.norm_coe_unitary_mul (star u) _
  calc
    _ ≤ (inner ℂ (T (u:A)) (T ((u:A)*∑ i, (star (b i)*b i+b i*star (b i))))).re := hsum
    _ ≤ ‖T (u:A)‖*‖T ((u:A)*∑ i, (star (b i)*b i+b i*star (b i)))‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ ≤ ‖T‖*(‖T‖*‖(u:A)*∑ i, (star (b i)*b i+b i*star (b i))‖) :=
      mul_le_mul hub (T.le_opNorm _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖T‖^2*‖∑ i, (star (b i)*b i+b i*star (b i))‖ := by
      rw [CStarRing.norm_coe_unitary_mul]; ring
    _ ≤ ‖T‖^2*(‖∑ i, star (b i)*b i‖+‖∑ i, b i*star (b i)‖) := by
      rw [Finset.sum_add_distrib]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (sq_nonneg _)
    _ = _ := by rw [hc,hr]

end Kadison.LittleGrothendieck

end

end
end

end OAI
