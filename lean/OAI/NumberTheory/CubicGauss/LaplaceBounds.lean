import Mathlib
import OAI.NumberTheory.CubicGauss.GaussianKernel

namespace OAI

/-! Weighted Gaussian tails and Laplace estimates for sieve kernels. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.SieveKernel

lemma factorial_term_le (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    r^n / n.factorial ≤ 6^n * Real.exp (r/6) := by
  have h := Real.pow_div_factorial_le_exp (r/6) (show 0 ≤ r/6 by positivity) n
  calc
    _ = 6^n * ((r/6)^n / n.factorial) := by rw [← mul_div_assoc, ← mul_pow]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

lemma damped_coefficient_bound (r : ℝ) (hr : 0 ≤ r) (v : Index) :
    ‖coefficient r v * (Real.exp (r/2) : ℂ)‖ ≤ 6^(v.1+v.2.1+v.2.2) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := coefficient_norm_le hr (le_refl r) (le_refl r) v
  have he : Real.exp (-r) * Real.exp (r/6) * Real.exp (r/6) *
      Real.exp (r/6) * Real.exp (r/2) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  calc
    _ ≤ (Real.exp (-r) * (r^v.1/v.1.factorial) *
      (r^v.2.1/v.2.1.factorial) * (r^v.2.2/v.2.2.factorial)) * Real.exp (r/2) := by gcongr
    _ ≤ (Real.exp (-r) * (6^v.1*Real.exp (r/6)) *
      (6^v.2.1*Real.exp (r/6)) * (6^v.2.2*Real.exp (r/6))) * Real.exp (r/2) := by
        gcongr
        · exact factorial_term_le r hr _
        · exact factorial_term_le r hr _
        · exact factorial_term_le r hr _
    _ = (6^v.1 * 6^v.2.1 * 6^v.2.2) *
      (Real.exp (-r) * Real.exp (r/6) * Real.exp (r/6) * Real.exp (r/6) * Real.exp (r/2)) := by ring
    _ = _ := by rw [he,mul_one,pow_add,pow_add]

lemma damping_cancel (r : ℝ) :
    (Real.exp (r/2) : ℂ) * (Real.exp (-r/4) : ℂ) * (Real.exp (-r/4) : ℂ) = 1 := by
  have h : Real.exp (r/2) * Real.exp (-r/4) * Real.exp (-r/4) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  exact_mod_cast h

def geometricMajorant (v : Index) : ℝ :=
  (3/5)^v.1 * (3/5)^v.2.1 * (3/50)^v.2.2

lemma geometricMajorant_hasSum : HasSum geometricMajorant (625/94 : ℝ) := by
  have h1 := hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (3/5 : ℝ)) (by norm_num : (3/5 : ℝ) < 1)
  have h2 := hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (3/50 : ℝ)) (by norm_num : (3/50 : ℝ) < 1)
  have h := hasSum_mul_real h1 (hasSum_mul_real h1 h2)
  norm_num at h
  exact h.congr_fun (fun v => by dsimp [geometricMajorant]; ring)

 

theorem gaussian_weighted_gram_bound {ι θ : Type*} (H : Finset ι) (S : Finset θ)
    (χ : ι → θ → ℂ) (u : θ → ℂ) (x : θ → ℝ) (r : ι → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hx : ∀ a ∈ S, |x a| ≤ (1/10 : ℝ))
    (hr : ∀ h ∈ H, 0 ≤ r h)
    (hop : ∀ v : θ → ℂ,
      ∑ h ∈ H, Real.exp (-r h/2) * ‖∑ a ∈ S, v a * χ h a‖^2 ≤
        K * ∑ a ∈ S, ‖v a‖^2) :
    ‖∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S,
      (u a * χ h a) * star (u b * χ h b) *
        Complex.exp (-(r h : ℂ)*(1-x a)*(1-x b))‖ ≤
      7 * K * ∑ a ∈ S, ‖u a‖^2 := by
  let ψ : ι → θ → ℂ := fun h a => (Real.exp (-r h/4) : ℂ) * χ h a
  have hsum (h : ι) (v : θ → ℂ) :
      ∑ a ∈ S, v a * ψ h a = (Real.exp (-r h/4) : ℂ) * ∑ a ∈ S, v a * χ h a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [ψ]
    ring
  have hψ (v : θ → ℂ) : ∑ h ∈ H, ‖∑ a ∈ S, v a * ψ h a‖^2 ≤ K * ∑ a ∈ S, ‖v a‖^2 := by
    convert hop v using 1
    apply Finset.sum_congr rfl
    intro h hh
    rw [hsum, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add]
    congr 2
    ring
  let D := K * ∑ a ∈ S, ‖u a‖^2
  have hD : 0 ≤ D := mul_nonneg hK (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  let F : Index → ℂ := fun v => ∑ h ∈ H,
    (coefficient (r h) v * (Real.exp (r h/2) : ℂ)) *
      (∑ a ∈ S, (u a * (x a : ℂ)^(v.1+v.2.2)) * ψ h a) *
      star (∑ a ∈ S, (u a * (x a : ℂ)^(v.2.1+v.2.2)) * ψ h a)
  have hF (v : Index) : F v = ∑ h ∈ H, coefficient (r h) v *
      (∑ a ∈ S, (u a * (x a : ℂ)^(v.1+v.2.2)) * χ h a) *
      star (∑ a ∈ S, (u a * (x a : ℂ)^(v.2.1+v.2.2)) * χ h a) := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [hsum,hsum,star_mul,Complex.star_def,Complex.conj_ofReal]
    have hc := damping_cancel (r h)
    calc
      _ = ((Real.exp (r h/2) : ℂ) * (Real.exp (-r h/4) : ℂ) * (Real.exp (-r h/4) : ℂ)) *
        (coefficient (r h) v * (∑ a ∈ S, (u a * (x a : ℂ)^(v.1+v.2.2)) * χ h a) *
          star (∑ a ∈ S, (u a * (x a : ℂ)^(v.2.1+v.2.2)) * χ h a)) := by simp only [Complex.star_def]; ring
      _ = _ := by rw [hc,one_mul]; rfl
  have hs : HasSum F (∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S,
      (u a * χ h a) * star (u b * χ h b) *
        Complex.exp (-(r h : ℂ)*(1-x a)*(1-x b))) := by
    have hs := hasSum_sum (s := H) fun h _ => hasSum_sum (s := S) fun a _ =>
      hasSum_sum (s := S) fun b _ =>
        (kernel_hasSum (r h) (x a) (x b)).mul_left ((u a * χ h a) * star (u b * χ h b))
    apply hs.congr_fun
    intro v
    rw [hF]
    apply Finset.sum_congr rfl
    intro h hh
    rw [star_sum,mul_assoc,Finset.sum_mul_sum]
    simp only [Finset.mul_sum,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hf (v : Index) : ‖F v‖ ≤ geometricMajorant v * D := by
    have hb := norm_weighted_pair_sum H
      (fun h => ∑ a ∈ S, (u a * (x a : ℂ)^(v.1+v.2.2)) * ψ h a)
      (fun h => ∑ a ∈ S, (u a * (x a : ℂ)^(v.2.1+v.2.2)) * ψ h a)
      (fun h => coefficient (r h) v * (Real.exp (r h/2) : ℂ))
      (show 0 ≤ (6:ℝ)^(v.1+v.2.1+v.2.2) by positivity)
      (show 0 ≤ Real.sqrt D * (1/10:ℝ)^(v.1+v.2.2) by positivity)
      (show 0 ≤ Real.sqrt D * (1/10:ℝ)^(v.2.1+v.2.2) by positivity)
      (fun h hh => damped_coefficient_bound (r h) (hr h hh) v)
      (power_coefficient_energy H S ψ u x (by norm_num) hK hx hψ _)
      (power_coefficient_energy H S ψ u x (by norm_num) hK hx hψ _)
    apply hb.trans_eq
    calc
      _ = (Real.sqrt D)^2 *
        ((6*(1/10:ℝ))^v.1 * (6*(1/10:ℝ))^v.2.1 * (6*(1/10:ℝ)^2)^v.2.2) := by
          generalize (1/10:ℝ) = d
          simp only [pow_add,mul_pow]
          ring
      _ = _ := by rw [Real.sq_sqrt hD]; norm_num [geometricMajorant]; ring
  have hb := hs.norm_le_of_bounded (geometricMajorant_hasSum.mul_right D) hf
  apply hb.trans
  change (625/94:ℝ)*D ≤ 7*K*∑ a ∈ S, ‖u a‖^2
  rw [mul_assoc]
  change (625/94:ℝ)*D ≤ 7*D
  exact mul_le_mul_of_nonneg_right (by norm_num) hD



open Set MeasureTheory

lemma exp_tail_indicator_integrable (n : ℝ) :
    IntegrableOn ((Ioi n).indicator fun y : ℝ => Real.exp (-y)) (Ioi 0) :=
  (integrableOn_exp_neg_Ioi 0).indicator measurableSet_Ioi

lemma exp_tail_indicator (n : ℝ) (hn : 0 ≤ n) :
    ∫ y : ℝ in Ioi 0, (Ioi n).indicator (fun y => Real.exp (-y)) y = Real.exp (-n) := by
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr]
  · simpa using integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) n
  · exact fun y hy => hn.trans_lt hy

 

lemma finite_laplace_identity {ι : Type*} (H : Finset ι) (n f : ι → ℝ)
    (hn : ∀ h ∈ H, 0 ≤ n h) :
    ∑ h ∈ H, Real.exp (-n h) * f h =
      ∫ y : ℝ in Ioi 0, Real.exp (-y) * ∑ h ∈ H with n h < y, f h := by
  classical
  have hrewrite (y : ℝ) : Real.exp (-y) * ∑ h ∈ H with n h < y, f h =
      ∑ h ∈ H, ((Ioi (n h)).indicator (fun y => Real.exp (-y)) y) * f h := by
    rw [Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hy : n h < y <;> simp [Set.indicator,hy]
  simp_rw [hrewrite]
  rw [integral_finsetSum H (fun h hh => (exp_tail_indicator_integrable (n h)).mul_const (f h))]
  apply Finset.sum_congr rfl
  intro h hh
  rw [integral_mul_const,exp_tail_indicator (n h) (hn h hh)]

 
theorem finite_laplace_bound {ι : Type*} (H : Finset ι) (n f : ι → ℝ)
    {X : ℝ} (hX : 0 < X) (hn : ∀ h ∈ H, 0 ≤ n h)
    (F : ℝ → ℝ)
    (hF : IntegrableOn (fun y => Real.exp (-y) * F (X*y)) (Ioi 0))
    (hcut : ∀ Y : ℝ, 0 < Y → ∑ h ∈ H with n h < Y, f h ≤ F Y) :
    ∑ h ∈ H, Real.exp (-n h/X) * f h ≤
      ∫ y : ℝ in Ioi 0, Real.exp (-y) * F (X*y) := by
  classical
  rw [show (fun h => Real.exp (-n h/X)*f h) =
      (fun h => Real.exp (-(n h/X))*f h) by funext h; rw [neg_div],
    finite_laplace_identity H (fun h => n h/X) f (fun h hh => div_nonneg (hn h hh) hX.le)]
  have hi : IntegrableOn
      (fun y => Real.exp (-y) * ∑ h ∈ H with n h/X < y, f h) (Ioi 0) := by
    have he (y : ℝ) : Real.exp (-y) * ∑ h ∈ H with n h/X < y, f h =
        ∑ h ∈ H, ((Ioi (n h/X)).indicator (fun y => Real.exp (-y)) y) * f h := by
      rw [Finset.sum_filter,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hy : n h/X < y <;> simp [Set.indicator,hy]
    simp_rw [he]
    exact integrable_finsetSum H (fun h hh => (exp_tail_indicator_integrable (n h/X)).mul_const (f h))
  apply setIntegral_mono_on hi hF measurableSet_Ioi
  intro y hy
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have he : H.filter (fun h => n h/X < y) = H.filter (fun h => n h < X*y) := by
    ext h
    simp only [Finset.mem_filter,div_lt_iff₀ hX]
    rw [mul_comm y X]
  rw [he]
  exact hcut (X*y) (mul_pos hX hy)

lemma laplace_rpow_integrable {p X : ℝ} (hp : -1 < p) (hX : 0 ≤ X) :
    IntegrableOn (fun y : ℝ => Real.exp (-y) * (X*y)^p) (Ioi 0) := by
  have hi := (Real.GammaIntegral_convergent (show 0 < p+1 by linarith)).const_mul (X^p)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro y hy
  dsimp only
  rw [Real.mul_rpow hX hy.le]
  simp only [add_sub_cancel_right]
  ring

lemma laplace_rpow_integral {p X : ℝ} (hp : -1 < p) (hX : 0 ≤ X) :
    ∫ y : ℝ in Ioi 0, Real.exp (-y) * (X*y)^p = X^p * Real.Gamma (p+1) := by
  calc
    _ = ∫ y : ℝ in Ioi 0, X^p * (y^((p+1)-1) * Real.exp (-(1*y))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [Real.mul_rpow hX hy.le]
      simp only [add_sub_cancel_right,one_mul]
      ring
    _ = _ := by
      rw [integral_const_mul,Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by norm_num)]
      simp

 

theorem finite_laplace_power_bound {ι : Type*} (H : Finset ι) (n f : ι → ℝ)
    {X C p : ℝ} (hX : 0 < X) (hp : -1 < p) (hn : ∀ h ∈ H, 0 ≤ n h)
    (hcut : ∀ Y : ℝ, 0 < Y → ∑ h ∈ H with n h < Y, f h ≤ C * Y^p) :
    ∑ h ∈ H, Real.exp (-n h/X) * f h ≤ C * X^p * Real.Gamma (p+1) := by
  have hi := (laplace_rpow_integrable hp hX.le).const_mul C
  have hi' : IntegrableOn (fun y => Real.exp (-y) * (C * (X*y)^p)) (Ioi 0) := by
    change Integrable _ _
    convert hi using 1
    funext y
    ring
  have hb := finite_laplace_bound H n f hX hn (fun Y => C*Y^p) hi' hcut
  apply hb.trans_eq
  calc
    _ = C * ∫ y : ℝ in Ioi 0, Real.exp (-y) * (X*y)^p := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      ring
    _ = _ := by rw [laplace_rpow_integral hp hX.le]; ring

end CubicFirstMoment.SieveKernel

namespace CubicFirstMoment.SieveKernel

 

open Set MeasureTheory

theorem finite_laplace_polynomial_bound {ι θ : Type*} (H : Finset ι) (J : Finset θ)
    (n f : ι → ℝ) (a p : θ → ℝ) {X : ℝ} (hX : 0<X)
    (hp : ∀ j ∈ J,-1<p j) (hn : ∀ h ∈ H,0≤n h)
    (hcut : ∀ Y : ℝ,0<Y → ∑ h ∈ H with n h<Y,f h ≤ ∑ j ∈ J,a j*Y^(p j)) :
    ∑ h ∈ H,Real.exp (-n h/X)*f h ≤ ∑ j ∈ J,a j*X^(p j)*Real.Gamma (p j+1) := by
  have hi (j : θ) (hj : j∈J) : IntegrableOn
      (fun y : ℝ => Real.exp (-y)*(a j*(X*y)^(p j))) (Ioi 0) := by
    have hi := (laplace_rpow_integrable (hp j hj) hX.le).const_mul (a j)
    change Integrable _ _
    convert hi using 1
    funext y
    ring
  have hF : IntegrableOn
      (fun y : ℝ => Real.exp (-y)*∑ j ∈ J,a j*(X*y)^(p j)) (Ioi 0) := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum J hi
  apply (finite_laplace_bound H n f hX hn (fun Y => ∑ j ∈ J,a j*Y^(p j)) hF hcut).trans_eq
  simp only [Finset.mul_sum]
  rw [integral_finsetSum J hi]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = a j*∫ y : ℝ in Ioi 0,Real.exp (-y)*(X*y)^(p j) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      ring
    _ = _ := by rw [laplace_rpow_integral (hp j hj) hX.le]; ring

lemma finite_laplace_three_bound {ι : Type*} (H : Finset ι) (n f : ι → ℝ)
    {X a b c p q s : ℝ} (hX : 0<X) (hp : -1<p) (hq : -1<q) (hs : -1<s)
    (hn : ∀ h ∈ H,0≤n h)
    (hcut : ∀ Y : ℝ,0<Y → ∑ h ∈ H with n h<Y,f h ≤ a*Y^p+b*Y^q+c*Y^s) :
    ∑ h ∈ H,Real.exp (-n h/X)*f h ≤
      a*X^p*Real.Gamma (p+1)+b*X^q*Real.Gamma (q+1)+c*X^s*Real.Gamma (s+1) := by
  have h := finite_laplace_polynomial_bound H (Finset.univ : Finset (Fin 3))
    n f ![a,b,c] ![p,q,s] hX (by
      intro j hj
      fin_cases j <;> simp [hp,hq,hs]) hn (by
      intro Y hY
      simpa [Fin.sum_univ_succ,add_assoc] using hcut Y hY)
  simpa [Fin.sum_univ_succ,add_assoc] using h

end CubicFirstMoment.SieveKernel
end

end OAI
