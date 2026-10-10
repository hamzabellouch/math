import OAI.Combinatorics.HoneycombChords.HyperbolicTransform

namespace OAI

/-! Polynomial and proper rational transforms and surjectivity onto finite interpolation data.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Filter Topology MeasureTheory

noncomputable def integralJet (u : ℝ) (j : ℕ) (m : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), transformJet u j m z

lemma integralJet_hasDerivAt {u m : ℝ} (j : ℕ)
    (h : |m| + |u| < Real.pi / 2) :
    HasDerivAt (integralJet u j) (integralJet u (j+1) m) m := by
  let a := (Real.pi / 2 + (|u| + |m|)) / 2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha : |u| + |m| < a := by dsimp [a]; linarith
  have hA : a < Real.pi / 2 := by dsimp [a]; linarith
  let s := {t : ℝ | |u| + |t| < a}
  have hs : s ∈ 𝓝 m :=
    (isOpen_lt (continuous_const.add continuous_abs) continuous_const).mem_nhds ha
  have hmeas : ∀ j t, AEStronglyMeasurable (transformJet u j t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro j t
    exact (by unfold transformJet hypJet; fun_prop : Measurable (transformJet u j t)).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.Eventually.of_forall (fun t => hmeas j t)) (transformJet_integrable j h) (hmeas (j+1) m)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      intro t ht
      exact transformJet_norm_le (j+1) hz.le (le_of_lt ht))
    (polynomial_kernel_integrable j ha0 hA)
    (ae_of_all _ (fun z t _ => transformJet_hasDerivAt u j t z))).2

lemma integralJet_zero_eq {u m : ℝ} (h : |m| + |u| < Real.pi / 2) :
    integralJet u 0 m = Real.sin (2*m) / (Real.cos (2*u) + Real.cos (2*m)) := by
  simpa only [integralJet, transformJet_zero] using cosh_sinh_kernel_integral h

lemma integralJet_eq_iteratedDeriv {u m : ℝ} (j : ℕ)
    (h : |m| + |u| < Real.pi / 2) :
    integralJet u j m =
      iteratedDeriv j (fun t => Real.sin (2*t) / (Real.cos (2*u) + Real.cos (2*t))) m := by
  induction j generalizing m with
  | zero => exact integralJet_zero_eq h
  | succ j ih =>
    have hs : ∀ᶠ t in 𝓝 m, |t| + |u| < Real.pi / 2 :=
      (isOpen_lt (continuous_abs.add continuous_const) continuous_const).mem_nhds h
    have he : integralJet u j =ᶠ[𝓝 m]
        iteratedDeriv j (fun t => Real.sin (2*t) / (Real.cos (2*u) + Real.cos (2*t))) :=
      hs.mono (fun t ht => ih ht)
    rw [iteratedDeriv_succ, ← he.deriv_eq]
    exact (integralJet_hasDerivAt j h).deriv.symm

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real MeasureTheory Filter Topology Polynomial Finset

lemma hypJet_odd (j : ℕ) (t : ℝ) : hypJet (2*j+1) t = Real.cosh t := by
  simp [hypJet, pow_add, pow_mul, Real.cosh_eq]

noncomputable def polynomialTransformJet (p : Polynomial ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  p.sum (fun j a => a * integralJet 0 (2*j+1+k) u)

lemma polynomialTransformJet_hasDerivAt (p : Polynomial ℝ) (k : ℕ) {u : ℝ}
    (hu : |u| < Real.pi/2) :
    HasDerivAt (polynomialTransformJet p k) (polynomialTransformJet p (k+1) u) u := by
  unfold polynomialTransformJet Polynomial.sum
  have hd (j : ℕ) := (integralJet_hasDerivAt (2*j+1+k)
    (by simpa using hu : |u| + |(0:ℝ)| < Real.pi/2)).const_mul (p.coeff j)
  simpa only [Nat.add_assoc] using HasDerivAt.fun_sum (fun j (_ : j ∈ p.support) => hd j)

lemma polynomialTransformJet_add (p q : Polynomial ℝ) (k : ℕ) (u : ℝ) :
    polynomialTransformJet (p+q) k u = polynomialTransformJet p k u + polynomialTransformJet q k u := by
  unfold polynomialTransformJet
  exact Polynomial.sum_add_index p q _ (by intros; simp) (by intros; ring)

lemma polynomialTransformJet_smul (a : ℝ) (p : Polynomial ℝ) (k : ℕ) (u : ℝ) :
    polynomialTransformJet (a • p) k u = a * polynomialTransformJet p k u := by
  unfold polynomialTransformJet
  rw [Polynomial.sum_smul_index p a _ (by intros; simp)]
  simp only [Polynomial.sum, Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

lemma polynomialTransformJet_X_mul (p : Polynomial ℝ) (k : ℕ) (u : ℝ) :
    polynomialTransformJet (X*p) k u = polynomialTransformJet p (k+2) u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, polynomialTransformJet_add, polynomialTransformJet_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.X_mul_monomial]
    simp only [polynomialTransformJet, Polynomial.sum_monomial_index, zero_mul]
    congr 2
    omega

lemma polynomialTransformJet_C (a : ℝ) (k : ℕ) (u : ℝ) :
    polynomialTransformJet (Polynomial.C a) k u = a * integralJet 0 (1+k) u := by
  simp [polynomialTransformJet, Polynomial.sum_C_index]

lemma polynomialTransformJet_two {p : Polynomial ℝ} {u : ℝ} (hu : |u| < Real.pi/2) :
    iteratedDeriv 2 (polynomialTransformJet p 0) u = polynomialTransformJet (X*p) 0 u := by
  have hn : ∀ᶠ t in 𝓝 u, |t| < Real.pi/2 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hu
  have he : deriv (polynomialTransformJet p 0) =ᶠ[𝓝 u] polynomialTransformJet p 1 :=
    hn.mono (fun t ht => (polynomialTransformJet_hasDerivAt p 0 ht).deriv)
  rw [show iteratedDeriv 2 (polynomialTransformJet p 0) = deriv (deriv (polynomialTransformJet p 0)) by rw [iteratedDeriv_succ, iteratedDeriv_one],
    he.deriv_eq, (polynomialTransformJet_hasDerivAt p 1 hu).deriv, polynomialTransformJet_X_mul]

noncomputable def polynomialKernel (p : Polynomial ℝ) (u z : ℝ) : ℝ :=
  p.eval (z^2) * Real.cosh (u*z) * z / Real.sinh (Real.pi*z/2)

lemma polynomialKernel_eq_sum (p : Polynomial ℝ) (u z : ℝ) :
    polynomialKernel p u z =
      ∑ j ∈ p.support, p.coeff j * transformJet 0 (2*j+1) u z := by
  simp only [polynomialKernel, Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [transformJet, zero_mul, Real.cosh_zero, one_mul, hypJet_odd]
  rw [pow_add, pow_one, pow_mul]
  ring

lemma polynomialKernel_integrable (p : Polynomial ℝ) {u : ℝ} (hu : |u| < Real.pi/2) :
    IntegrableOn (polynomialKernel p u) (Set.Ioi 0) := by
  have h : ∀ j, IntegrableOn (fun z => p.coeff j * transformJet 0 (2*j+1) u z) (Set.Ioi 0) :=
    fun j => (transformJet_integrable (2*j+1) (by simpa using hu)).const_mul (p.coeff j)
  simpa only [IntegrableOn, ← polynomialKernel_eq_sum] using integrable_finsetSum p.support (fun j _ => h j)

lemma polynomialTransform_eq_integral (p : Polynomial ℝ) {u : ℝ} (hu : |u| < Real.pi/2) :
    polynomialTransformJet p 0 u = ∫ z in Set.Ioi (0:ℝ), polynomialKernel p u z := by
  simp only [polynomialKernel_eq_sum]
  rw [integral_finsetSum p.support (fun j _ =>
    (transformJet_integrable (2*j+1) (by simpa using hu)).const_mul (p.coeff j))]
  simp only [integral_const_mul, polynomialTransformJet, Polynomial.sum, Nat.add_zero, integralJet]

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section
namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Finset
lemma triangular_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v w : ℕ → V) (c : ℕ → ℕ → K)
    (hw : ∀ k,w k=∑ j ∈ range (k+1),c k j • v j)
    (hc : ∀ k,c k k ≠ 0) (N : ℕ) :
    Submodule.span K (v '' Set.Iio N) = Submodule.span K (w '' Set.Iio N) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,rfl⟩
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hwk : w k ∈ Submodule.span K (w '' Set.Iio N) := Submodule.subset_span ⟨k,hk,rfl⟩
      have hsum : (∑ j ∈ range k,c k j • v j) ∈ Submodule.span K (w '' Set.Iio N) := by
        apply Submodule.sum_mem
        intro j hj
        exact Submodule.smul_mem _ _ (ih j (mem_range.mp hj) (lt_trans (mem_range.mp hj) hk))
      rw [hw, sum_range_succ] at hwk
      have hmem := Submodule.sub_mem _ hwk hsum
      simp only [add_sub_cancel_left] at hmem
      have hmem' := Submodule.smul_mem (Submodule.span K (w '' Set.Iio N)) (c k k)⁻¹ hmem
      rw [smul_smul,inv_mul_cancel₀ (hc k),one_smul] at hmem'
      exact hmem'
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,rfl⟩
    rw [hw]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j,lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hj)) hk,rfl⟩
end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Finset Filter Topology

noncomputable def poleCoeff (a b : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, 0 => a
  | 0, _+1 => 0
  | n+1, 0 => deriv (poleCoeff a b n 0)
  | n+1, k+1 => fun m => deriv (poleCoeff a b n (k+1)) m -
      (k+1 : ℕ) * deriv b m * poleCoeff a b n k m

lemma poleCoeff_smooth {a b : ℝ → ℝ} (ha : ContDiff ℝ ⊤ a)
    (hb : ContDiff ℝ ⊤ b) (n k : ℕ) : ContDiff ℝ ⊤ (poleCoeff a b n k) := by
  induction n generalizing k with
  | zero => cases k <;> simp only [poleCoeff]; exact ha; exact contDiff_const
  | succ n ih =>
    cases k with
    | zero => exact (ih 0).deriv'
    | succ k =>
      exact (ih (k+1)).deriv'.sub ((contDiff_const.mul hb.deriv').mul (ih k))

lemma poleCoeff_eq_zero {a b : ℝ → ℝ} {n k : ℕ} (h : n < k) :
    poleCoeff a b n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> first | omega | rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      have h1 := ih (show n < k+1 by omega)
      have h2 := ih (show n < k by omega)
      ext m
      simp [poleCoeff, h1, h2]

lemma poleCoeff_diagonal_ne_zero {a b : ℝ → ℝ} {m : ℝ}
    (ha : a m ≠ 0) (hb : deriv b m ≠ 0) (n : ℕ) : poleCoeff a b n n m ≠ 0 := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    have hz := poleCoeff_eq_zero (a:=a) (b:=b) (show n < n+1 by omega)
    change deriv (poleCoeff a b n (n+1)) m -
      (n+1 : ℕ) * deriv b m * poleCoeff a b n n m ≠ 0
    rw [hz, show deriv (0 : ℝ → ℝ) m = 0 from deriv_const m 0, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) hb) ih)

lemma reciprocal_power_hasDerivAt {b : ℝ → ℝ} {m X : ℝ} (k : ℕ)
    (hb : DifferentiableAt ℝ b m) (hXm : X + b m ≠ 0) :
    HasDerivAt (fun t => (X + b t)⁻¹ ^ (k+1))
      (-(k+1:ℕ) * deriv b m * (X + b m)⁻¹ ^ (k+2)) m := by
  have h := ((hb.hasDerivAt.const_add X).inv hXm).pow (k+1)
  convert h using 1; try rfl
  simp only [Pi.inv_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, ← inv_pow]
  ring


lemma poleJet_expansion {a b : ℝ → ℝ} (ha : ContDiff ℝ ⊤ a)
    (hb : ContDiff ℝ ⊤ b) (n : ℕ) {m X : ℝ} (hXm : X + b m ≠ 0) :
    iteratedDeriv n (fun t => a t / (X + b t)) m =
      ∑ k ∈ range (n+1), poleCoeff a b n k m * (X+b m)⁻¹ ^ (k+1) := by
  induction n generalizing m with
  | zero => simp [poleCoeff, div_eq_mul_inv]
  | succ n ih =>
    have he : iteratedDeriv n (fun t => a t / (X+b t)) =ᶠ[𝓝 m]
        (fun t => ∑ k ∈ range (n+1), poleCoeff a b n k t * (X+b t)⁻¹ ^ (k+1)) := by
      filter_upwards [(continuous_const.add hb.continuous).continuousAt.eventually_ne hXm] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hd (k : ℕ) := ((poleCoeff_smooth ha hb n k).differentiable (by simp)).differentiableAt.hasDerivAt.mul
      (reciprocal_power_hasDerivAt k (hb.differentiable (by simp)).differentiableAt hXm)
    have hds := HasDerivAt.fun_sum (fun k (_ : k ∈ range (n+1)) => hd k)
    simp only [Pi.mul_apply] at hds
    rw [hds.deriv]
    have hz : deriv (poleCoeff a b n (n+1)) m = 0 := by
      rw [poleCoeff_eq_zero (by omega)]
      exact deriv_const m 0
    let A := fun k => deriv (poleCoeff a b n k) m * (X+b m)⁻¹ ^ (k+1)
    have hshift : (∑ k ∈ range (n+1), A k) =
        A 0 + ∑ k ∈ range (n+1), A (k+1) := by
      have h1 := sum_range_succ A (n+1)
      have h2 := sum_range_succ' A (n+1)
      have hzero : A (n+1) = 0 := by simp only [A, hz, zero_mul]
      rw [hzero, add_zero] at h1
      rw [h1] at h2
      exact h2.trans (add_comm _ _)
    calc
      (∑ k ∈ range (n+1),
          (deriv (poleCoeff a b n k) m * (X+b m)⁻¹ ^ (k+1) +
          poleCoeff a b n k m * (-(k+1:ℕ) * deriv b m * (X+b m)⁻¹ ^ (k+2))))
          = (∑ k ∈ range (n+1), A k) -
            ∑ k ∈ range (n+1), (k+1:ℕ) * deriv b m * poleCoeff a b n k m * (X+b m)⁻¹ ^ (k+2) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro k hk
        dsimp [A]
        ring
      _ = A 0 + ∑ k ∈ range (n+1),
          (deriv (poleCoeff a b n (k+1)) m - (k+1:ℕ) * deriv b m * poleCoeff a b n k m) *
            (X+b m)⁻¹ ^ (k+2) := by
        rw [hshift, add_sub_assoc, ← sum_sub_distrib]
        congr 1
        apply sum_congr rfl
        intro k hk
        dsimp [A]
        ring
      _ = ∑ k ∈ range (n+1+1), poleCoeff a b (n+1) k m * (X+b m)⁻¹ ^ (k+1) := by
        conv_rhs => rw [sum_range_succ']
        simp only [poleCoeff, A, Nat.zero_add, pow_one]
        rw [add_comm]

lemma poleJet_span {ι : Type*} (X : ι → ℝ) {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ⊤ a) (hb : ContDiff ℝ ⊤ b) {m : ℝ}
    (ham : a m ≠ 0) (hbm : deriv b m ≠ 0) (hden : ∀ i, X i + b m ≠ 0) (N : ℕ) :
    Submodule.span ℂ ((fun k : ℕ => fun i => (((X i+b m)⁻¹ ^ (k+1) : ℝ) : ℂ)) '' Set.Iio N) =
    Submodule.span ℂ ((fun k : ℕ => fun i => ((iteratedDeriv k (fun t => a t / (X i+b t)) m : ℝ) : ℂ)) '' Set.Iio N) := by
  apply triangular_span _ _ (fun n k => (poleCoeff a b n k m : ℂ))
  · intro k
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [poleJet_expansion ha hb k (hden i)]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  · intro k
    exact Complex.ofReal_ne_zero.mpr (poleCoeff_diagonal_ne_zero ham hbm k)

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Filter Topology

noncomputable def reciprocalCosinePower (n : ℕ) (u : ℝ) : ℝ :=
  (1+Real.cos (2*u))⁻¹ ^ n

lemma cosineDouble_hasDerivAt (u : ℝ) :
    HasDerivAt (fun t => Real.cos (2*t)) (-2*Real.sin (2*u)) u := by
  convert ((hasDerivAt_id u).const_mul 2).cos using 1 <;> simp only [id_eq, mul_one]
  ring

lemma sineDouble_hasDerivAt (u : ℝ) :
    HasDerivAt (fun t => Real.sin (2*t)) (2*Real.cos (2*u)) u := by
  convert ((hasDerivAt_id u).const_mul 2).sin using 1 <;> simp only [id_eq, mul_one]
  ring

lemma reciprocalCosinePower_hasDerivAt (n : ℕ) {u : ℝ}
    (hu : 1+Real.cos (2*u) ≠ 0) :
    HasDerivAt (reciprocalCosinePower (n+1))
      (2*(n+1:ℕ)*Real.sin (2*u)*reciprocalCosinePower (n+2) u) u := by
  have h := reciprocal_power_hasDerivAt (m:=u) (X:=1) n
    (cosineDouble_hasDerivAt u).differentiableAt hu
  rw [(cosineDouble_hasDerivAt u).deriv] at h
  convert h using 1; try rfl
  dsimp [reciprocalCosinePower]
  ring

lemma reciprocalCosinePower_two (n : ℕ) {u : ℝ}
    (hu : 1+Real.cos (2*u) ≠ 0) :
    iteratedDeriv 2 (reciprocalCosinePower (n+1)) u =
      4*(n+1:ℕ)*(2*(n+1:ℕ)+1)*reciprocalCosinePower (n+2) u -
        4*(n+1:ℕ)^2*reciprocalCosinePower (n+1) u := by
  have hn : ∀ᶠ t in 𝓝 u, 1+Real.cos (2*t) ≠ 0 :=
    (show Continuous (fun t : ℝ => 1+Real.cos (2*t)) by fun_prop).continuousAt.eventually_ne hu
  have he : deriv (reciprocalCosinePower (n+1)) =ᶠ[𝓝 u]
      (fun t => 2*(n+1:ℕ)*Real.sin (2*t)*reciprocalCosinePower (n+2) t) :=
    hn.mono (fun t ht => (reciprocalCosinePower_hasDerivAt n ht).deriv)
  rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  have hd := ((sineDouble_hasDerivAt u).const_mul (2*((n+1:ℕ):ℝ))).mul
    (reciprocalCosinePower_hasDerivAt (n+1) hu)
  change HasDerivAt (fun t => 2*(n+1:ℕ)*Real.sin (2*t)*reciprocalCosinePower (n+2) t) _ u at hd
  rw [hd.deriv]
  dsimp [reciprocalCosinePower]
  have hid := Real.sin_sq_add_cos_sq (2*u)
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  nlinarith [hid]

lemma reciprocalCosine_den_ne_zero {u : ℝ} (hu : |u| < Real.pi/2) :
    1+Real.cos (2*u) ≠ 0 := by
  have hc := Real.cos_pos_of_mem_Ioo (show u ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from abs_lt.mp hu)
  rw [Real.cos_two_mul]
  nlinarith [sq_pos_of_pos hc]

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real MeasureTheory Filter Topology Polynomial

lemma integralJet_one {u : ℝ} (hu : |u| < Real.pi/2) :
    integralJet 0 1 u = 2 / (1+Real.cos (2*u)) := by
  have hn := reciprocalCosine_den_ne_zero hu
  have hd := (sineDouble_hasDerivAt u).div
    ((cosineDouble_hasDerivAt u).const_add 1) hn
  rw [integralJet_eq_iteratedDeriv 1 (by simpa using hu), iteratedDeriv_one]
  simp only [mul_zero, Real.cos_zero]
  change HasDerivAt (fun t => Real.sin (2*t) / (1+Real.cos (2*t))) _ u at hd
  rw [hd.deriv]
  have hid := Real.sin_sq_add_cos_sq (2*u)
  field_simp
  nlinarith [hid]

noncomputable def inverseCosinePolynomial : ℕ → Polynomial ℝ
  | 0 => Polynomial.C (1/2)
  | n+1 => (4*(n+1:ℕ)*(2*(n+1:ℕ)+1) : ℝ)⁻¹ •
      (X * inverseCosinePolynomial n + (4*(n+1:ℕ)^2 : ℝ) • inverseCosinePolynomial n)

lemma inverseCosinePolynomial_degree (n : ℕ) :
    (inverseCosinePolynomial n).natDegree ≤ n := by
  induction n with
  | zero => simp [inverseCosinePolynomial]
  | succ n ih =>
    apply (natDegree_smul_le _ _).trans
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by simpa [Nat.add_comm] using Nat.add_le_add_left ih 1)
    · exact (natDegree_smul_le _ _).trans (ih.trans (Nat.le_succ n))

lemma inverseCosinePolynomial_transform (n : ℕ) {u : ℝ} (hu : |u| < Real.pi/2) :
    polynomialTransformJet (inverseCosinePolynomial n) 0 u = reciprocalCosinePower (n+1) u := by
  induction n generalizing u with
  | zero =>
    rw [inverseCosinePolynomial, polynomialTransformJet_C]
    simp only [Nat.add_zero]
    rw [integralJet_one hu]
    simp [reciprocalCosinePower, div_eq_mul_inv]
  | succ n ih =>
    have hn : ∀ᶠ t in 𝓝 u, |t| < Real.pi/2 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hu
    have he : polynomialTransformJet (inverseCosinePolynomial n) 0 =ᶠ[𝓝 u]
        reciprocalCosinePower (n+1) :=
      hn.mono (fun _ ht => ih ht)
    have htwo := he.iteratedDeriv_eq 2
    rw [polynomialTransformJet_two hu,
      reciprocalCosinePower_two n (reciprocalCosine_den_ne_zero hu)] at htwo
    rw [inverseCosinePolynomial, polynomialTransformJet_smul, polynomialTransformJet_add,
      polynomialTransformJet_smul, htwo, ih hu]
    have hnonzero : (4*(n+1:ℕ)*(2*(n+1:ℕ)+1) : ℝ) ≠ 0 := by positivity
    field_simp
    ring

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real MeasureTheory Filter Topology Polynomial Finset

noncomputable def zMonomial (j : ℕ) (z : ℝ) : ℂ := ((z^2)^j : ℝ)
noncomputable def zCoshJet (m : ℝ) (j : ℕ) (z : ℝ) : ℂ :=
  (z^j*hypJet (j+1) (m*z) : ℝ)
noncomputable def zG (m z : ℝ) : ℂ := (Real.sinh (m*z)/z : ℝ)
noncomputable def zDensity (m : ℝ) (N : ℕ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ
    (Set.range (fun j : Fin N => zMonomial j.val) ∪
     Set.range (fun j : Fin N => zCoshJet m j.val) ∪ {zG m})

noncomputable def zKernel (f : ℝ → ℂ) (u z : ℝ) : ℂ :=
  f z * (Real.cosh (u*z) : ℂ) * z / (Real.sinh (Real.pi*z/2) : ℂ)
noncomputable def zTransform (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ z in Set.Ioi (0:ℝ), zKernel f u z

def TransformDomain (m : ℝ) := {u : ℝ // |u|+|m| < Real.pi/2}

lemma zKernel_add (f g : ℝ → ℂ) (u : ℝ) :
    zKernel (f+g) u = zKernel f u + zKernel g u := by
  ext z
  simp only [zKernel, Pi.add_apply]
  ring
lemma zKernel_smul (c : ℂ) (f : ℝ → ℂ) (u : ℝ) :
    zKernel (c • f) u = c • zKernel f u := by
  ext z
  simp only [zKernel, Pi.smul_apply, smul_eq_mul]
  ring
lemma zKernel_zero (u : ℝ) : zKernel 0 u = 0 := by ext z; simp [zKernel]

lemma zKernel_monomial (j : ℕ) (u z : ℝ) :
    zKernel (zMonomial j) u z = (transformJet 0 (2*j+1) u z : ℝ) := by
  simp only [zKernel, zMonomial, transformJet, zero_mul, Real.cosh_zero, one_mul,
    hypJet_odd, pow_add, pow_one, pow_mul]
  push_cast
  ring
lemma zKernel_coshJet (m : ℝ) (j : ℕ) (u z : ℝ) :
    zKernel (zCoshJet m j) u z = (transformJet u (j+1) m z : ℝ) := by
  simp only [zKernel, zCoshJet, transformJet, pow_succ]
  push_cast
  ring
lemma zKernel_g (m u : ℝ) {z : ℝ} (hz : 0 < z) :
    zKernel (zG m) u z = (transformJet u 0 m z : ℝ) := by
  have hz0 : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  simp only [zKernel, zG, transformJet_zero]
  push_cast
  field_simp

lemma zKernel_monomial_integrable {u : ℝ} (hu : |u| < Real.pi/2) (j : ℕ) :
    IntegrableOn (zKernel (zMonomial j) u) (Set.Ioi 0) := by
  change Integrable (fun z => zKernel (zMonomial j) u z) _
  simp_rw [zKernel_monomial]
  exact (transformJet_integrable (u:=0) (m:=u) (2*j+1) (by simpa using hu)).ofReal (𝕜:=ℂ)
lemma zKernel_coshJet_integrable {m u : ℝ} (hu : |u|+|m| < Real.pi/2) (j : ℕ) :
    IntegrableOn (zKernel (zCoshJet m j) u) (Set.Ioi 0) := by
  change Integrable (fun z => zKernel (zCoshJet m j) u z) _
  simp_rw [zKernel_coshJet]
  exact (transformJet_integrable (u:=u) (m:=m) (j+1) (by linarith : |m|+|u| < Real.pi/2)).ofReal (𝕜:=ℂ)
lemma zKernel_g_integrable {m u : ℝ} (hu : |u|+|m| < Real.pi/2) :
    IntegrableOn (zKernel (zG m) u) (Set.Ioi 0) := by
  apply ((transformJet_integrable 0 (by linarith : |m|+|u| < Real.pi/2)).ofReal (𝕜:=ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact (zKernel_g m u hz).symm

lemma zDensity_integrable {m u : ℝ} {N : ℕ} {f : ℝ → ℂ}
    (hf : f ∈ zDensity m N) (hu : |u|+|m| < Real.pi/2) :
    IntegrableOn (zKernel f u) (Set.Ioi 0) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ((⟨j,rfl⟩ | ⟨j,rfl⟩) | rfl)
    · exact zKernel_monomial_integrable (by linarith [abs_nonneg m]) j.val
    · exact zKernel_coshJet_integrable hu j.val
    · exact zKernel_g_integrable hu
  | zero => rw [zKernel_zero]; exact integrable_zero _ _ _
  | add f g hf hg hfi hgi => rw [zKernel_add]; exact hfi.add hgi
  | smul c f hf hfi => rw [zKernel_smul]; exact hfi.smul c

lemma zTransform_add {f g : ℝ → ℂ} {u : ℝ}
    (hf : IntegrableOn (zKernel f u) (Set.Ioi 0))
    (hg : IntegrableOn (zKernel g u) (Set.Ioi 0)) :
    zTransform (f+g) u = zTransform f u + zTransform g u := by
  unfold zTransform
  rw [zKernel_add]
  simp only [Pi.add_apply]
  exact integral_add hf hg
lemma zTransform_smul (c : ℂ) (f : ℝ → ℂ) (u : ℝ) :
    zTransform (c • f) u = c * zTransform f u := by
  unfold zTransform
  rw [zKernel_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _
lemma zTransform_zero (u : ℝ) : zTransform 0 u = 0 := by simp [zTransform, zKernel_zero]

noncomputable def zTransformLinear (m : ℝ) (N : ℕ) :
    zDensity m N →ₗ[ℂ] (TransformDomain m → ℂ) where
  toFun f u := zTransform f.val u.val
  map_add' f g := funext (fun u => zTransform_add
    (zDensity_integrable f.property u.property) (zDensity_integrable g.property u.property))
  map_smul' c f := funext (fun u => zTransform_smul c f.val u.val)

lemma zTransform_monomial (j : ℕ) (u : ℝ) :
    zTransform (zMonomial j) u = (integralJet 0 (2*j+1) u : ℝ) := by
  simp only [zTransform, zKernel_monomial, _root_.integral_complex_ofReal, integralJet]
lemma zTransform_coshJet (m : ℝ) (j : ℕ) (u : ℝ) :
    zTransform (zCoshJet m j) u = (integralJet u (j+1) m : ℝ) := by
  simp only [zTransform, zKernel_coshJet, _root_.integral_complex_ofReal, integralJet]
lemma zTransform_g (m u : ℝ) :
    zTransform (zG m) u = (integralJet u 0 m : ℝ) := by
  unfold zTransform integralJet
  rw [← _root_.integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z hz
  exact zKernel_g m u hz

lemma zPolynomial_mem {m : ℝ} {N : ℕ} (p : Polynomial ℝ) (hp : p.natDegree < N) :
    (fun z => ((p.eval ((z:ℝ)^2) : ℝ) : ℂ)) ∈ zDensity m N := by
  have hs : (∑ j ∈ p.support, (p.coeff j : ℂ) • zMonomial j) ∈ zDensity m N := by
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Or.inl (Or.inl ⟨⟨j,(Polynomial.le_natDegree_of_mem_supp j hj).trans_lt hp⟩,rfl⟩)
  convert hs using 1
  ext z
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zMonomial]

lemma zTransform_polynomial (p : Polynomial ℝ) {u : ℝ} (hu : |u| < Real.pi/2) :
    zTransform (fun z => ((p.eval ((z:ℝ)^2) : ℝ) : ℂ)) u = (polynomialTransformJet p 0 u : ℝ) := by
  rw [polynomialTransform_eq_integral p hu]
  unfold zTransform
  rw [← _root_.integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z hz
  simp only [zKernel, polynomialKernel]
  push_cast
  rfl

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Polynomial Finset

lemma mixed_inverse_step {x a b : ℂ} (ha : x+a ≠ 0) (hb : x+b ≠ 0) (hab : b-a ≠ 0)
    (n m : ℕ) :
    (x+a)⁻¹^(n+1) * (x+b)⁻¹^(m+1) =
      (b-a)⁻¹ * ((x+a)⁻¹^(n+1) * (x+b)⁻¹^m - (x+a)⁻¹^n * (x+b)⁻¹^(m+1)) := by
  simp only [pow_succ]
  field_simp
  ring

lemma reciprocalProduct_mem {ι : Type*} (x : ι → ℂ) (a b : ℂ)
    (ha : ∀ i, x i+a ≠ 0) (hb : ∀ i, x i+b ≠ 0) (hab : b-a ≠ 0)
    (S : Submodule ℂ (ι → ℂ)) (N M : ℕ)
    (haS : ∀ k, 0<k → k≤N → (fun i => (x i+a)⁻¹^k) ∈ S)
    (hbS : ∀ k, 0<k → k≤M → (fun i => (x i+b)⁻¹^k) ∈ S)
    (n m : ℕ) (hn : n≤N) (hm : m≤M) (hpos : 0<n+m) :
    (fun i => (x i+a)⁻¹^n * (x i+b)⁻¹^m) ∈ S := by
  induction n generalizing m with
  | zero => simpa only [pow_zero, one_mul] using hbS m (by omega) hm
  | succ n ih =>
    induction m with
    | zero => simpa only [pow_zero, mul_one] using haS (n+1) (by omega) hn
    | succ m ihm =>
      have h1 := ihm (by omega) (by omega)
      have h2 := ih (m+1) (by omega) hm (by omega)
      have hs := S.smul_mem (b-a)⁻¹ (S.sub_mem h1 h2)
      convert hs using 1
      ext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      exact mixed_inverse_step (ha i) (hb i) hab n m

lemma monomial_inverse_step {x a b : ℂ} (ha : x+a ≠ 0) (j n m : ℕ) :
    x^(j+1) * (x+a)⁻¹^(n+1) * (x+b)⁻¹^m =
      x^j * (x+a)⁻¹^n * (x+b)⁻¹^m - a * (x^j * (x+a)⁻¹^(n+1) * (x+b)⁻¹^m) := by
  simp only [pow_succ]
  field_simp
  ring

lemma properMonomial_mem {ι : Type*} (x : ι → ℂ) (a b : ℂ)
    (ha : ∀ i, x i+a ≠ 0) (hb : ∀ i, x i+b ≠ 0) (hab : b-a ≠ 0)
    (S : Submodule ℂ (ι → ℂ)) (N M : ℕ)
    (haS : ∀ k, 0<k → k≤N → (fun i => (x i+a)⁻¹^k) ∈ S)
    (hbS : ∀ k, 0<k → k≤M → (fun i => (x i+b)⁻¹^k) ∈ S)
    (j n m : ℕ) (hn : n≤N) (hm : m≤M) (hj : j<n+m) :
    (fun i => x i^j * (x i+a)⁻¹^n * (x i+b)⁻¹^m) ∈ S := by
  induction j generalizing n m with
  | zero => simpa only [pow_zero, one_mul] using
      reciprocalProduct_mem x a b ha hb hab S N M haS hbS n m hn hm hj
  | succ j ih =>
    cases n with
    | succ n =>
      have h1 := ih n m (by omega) hm (by omega)
      have h2 := ih (n+1) m hn hm (by omega)
      have hs := S.sub_mem h1 (S.smul_mem a h2)
      convert hs using 1
      ext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      exact monomial_inverse_step (ha i) j n m
    | zero =>
      have hm0 : 0 < m :=  by omega
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm0)
      have h1 := ih 0 m hn (by omega) (by omega)
      have h2 := ih 0 (m+1) hn hm (by omega)
      have hs := S.sub_mem h1 (S.smul_mem b h2)
      convert hs using 1
      ext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, pow_zero, mul_one]
      simpa only [pow_zero, mul_one] using
        monomial_inverse_step (b:=a) (hb i) j m 0

lemma properPolynomial_mem {ι : Type*} (x : ι → ℂ) (a b : ℂ)
    (ha : ∀ i, x i+a ≠ 0) (hb : ∀ i, x i+b ≠ 0) (hab : b-a ≠ 0)
    (S : Submodule ℂ (ι → ℂ)) (N M : ℕ)
    (haS : ∀ k, 0<k → k≤N → (fun i => (x i+a)⁻¹^k) ∈ S)
    (hbS : ∀ k, 0<k → k≤M → (fun i => (x i+b)⁻¹^k) ∈ S)
    (p : Polynomial ℂ) (hp : p.natDegree < N+M) :
    (fun i => p.eval (x i) / ((x i+a)^N * (x i+b)^M)) ∈ S := by
  have hs : (∑ j ∈ p.support, p.coeff j • (fun i => x i^j * (x i+a)⁻¹^N * (x i+b)⁻¹^M)) ∈ S := by
    apply S.sum_mem
    intro j hj
    apply S.smul_mem
    exact properMonomial_mem x a b ha hb hab S N M haS hbS j N M le_rfl le_rfl
      ((le_natDegree_of_mem_supp j hj).trans_lt hp)
  convert hs using 1
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_div]
  apply sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Filter Topology Polynomial Finset

lemma cosine_sum_pos {u m : ℝ} (hu : |u|+|m| < Real.pi/2) :
    0 < Real.cos (2*u) + Real.cos (2*m) := by
  have hp : |u+m| < Real.pi/2 := (abs_add_le u m).trans_lt hu
  have hm : |u-m| < Real.pi/2 := (abs_sub u m).trans_lt hu
  have hcp := Real.cos_pos_of_mem_Ioo (abs_lt.mp hp)
  have hcm := Real.cos_pos_of_mem_Ioo (abs_lt.mp hm)
  rw [Real.cos_add_cos, show (2*u+2*m)/2 = u+m by ring, show (2*u-2*m)/2 = u-m by ring]
  exact mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hcp) hcm

lemma zMonomial_mem (m : ℝ) {N j : ℕ} (hj : j<N) : zMonomial j ∈ zDensity m N :=
  Submodule.subset_span (Or.inl (Or.inl ⟨⟨j,hj⟩,rfl⟩))
lemma zCoshJet_mem (m : ℝ) {N j : ℕ} (hj : j<N) : zCoshJet m j ∈ zDensity m N :=
  Submodule.subset_span (Or.inl (Or.inr ⟨⟨j,hj⟩,rfl⟩))
lemma zG_mem (m : ℝ) (N : ℕ) : zG m ∈ zDensity m N :=
  Submodule.subset_span (Or.inr rfl)

lemma firstPole_mem_range (m : ℝ) (N : ℕ) (k : ℕ) (hk : 0<k) (hkN : k≤N) :
    (fun u : TransformDomain m =>
      ((Real.cos (2*u.val):ℂ)+1)⁻¹^k) ∈ (zTransformLinear m N).range := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  let p := inverseCosinePolynomial n
  have hp : p.natDegree < N := (inverseCosinePolynomial_degree n).trans_lt (by omega)
  refine ⟨⟨fun z => ((p.eval ((z:ℝ)^2) : ℝ) : ℂ), zPolynomial_mem p hp⟩,?_⟩
  ext u
  have hu : |u.val| < Real.pi/2 := by linarith [u.property,abs_nonneg m]
  change zTransform (fun z => ((p.eval ((z:ℝ)^2) : ℝ) : ℂ)) u.val = _
  rw [zTransform_polynomial p hu, inverseCosinePolynomial_transform n hu]
  simp only [reciprocalCosinePower, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one]
  rw [add_comm]

lemma poleJet_mem_range (m : ℝ) (N : ℕ) (j : ℕ) (hj : j < N+1) :
    (fun u : TransformDomain m =>
      ((iteratedDeriv j (fun t => Real.sin (2*t) / (Real.cos (2*u.val)+Real.cos (2*t))) m : ℝ) : ℂ))
      ∈ (zTransformLinear m N).range := by
  cases j with
  | zero =>
    refine ⟨⟨zG m,zG_mem m N⟩,?_⟩
    ext u
    change zTransform (zG m) u.val = _
    rw [zTransform_g, integralJet_eq_iteratedDeriv 0 (by linarith [u.property])]
  | succ j =>
    refine ⟨⟨zCoshJet m j,zCoshJet_mem m (by omega)⟩,?_⟩
    ext u
    change zTransform (zCoshJet m j) u.val = _
    rw [zTransform_coshJet, integralJet_eq_iteratedDeriv (j+1) (by linarith [u.property])]

lemma secondPole_mem_range {m : ℝ} (hm : 0 < m) (hm' : m < Real.pi/2)
    (N : ℕ) (k : ℕ) (hk : 0<k) (hkN : k≤N+1) :
    (fun u : TransformDomain m =>
      ((Real.cos (2*u.val):ℂ)+(Real.cos (2*m):ℂ))⁻¹^k) ∈ (zTransformLinear m N).range := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  have hsm : Real.sin (2*m) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hbm : deriv (fun t => Real.cos (2*t)) m ≠ 0 := by
    rw [(cosineDouble_hasDerivAt m).deriv]
    exact mul_ne_zero (by norm_num) hsm
  have he := poleJet_span (fun u : TransformDomain m => Real.cos (2*u.val))
    (show ContDiff ℝ ⊤ (fun t => Real.sin (2*t)) by fun_prop)
    (show ContDiff ℝ ⊤ (fun t => Real.cos (2*t)) by fun_prop)
    hsm hbm (fun u => (cosine_sum_pos u.property).ne') (N+1)
  have hs : Submodule.span ℂ
      ((fun j : ℕ => fun u : TransformDomain m =>
        ((iteratedDeriv j (fun t => Real.sin (2*t) / (Real.cos (2*u.val)+Real.cos (2*t))) m : ℝ) : ℂ))
        '' Set.Iio (N+1)) ≤ (zTransformLinear m N).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    exact poleJet_mem_range m N j hj
  rw [← he] at hs
  have hv := hs (Submodule.subset_span ⟨n,(by change n < N+1; omega),rfl⟩)
  simpa only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_add] using hv

lemma zTransform_surjective {m : ℝ} (hm : 0 < m) (hm' : m < Real.pi/2)
    (N : ℕ) (p : Polynomial ℂ) (hp : p.natDegree < 2*N+1) :
    ∃ f ∈ zDensity m N, ∀ u : TransformDomain m,
      zTransform f u.val = p.eval (Real.cos (2*u.val):ℂ) /
        (((Real.cos (2*u.val):ℂ)+1)^N *
          ((Real.cos (2*u.val):ℂ)+(Real.cos (2*m):ℂ))^(N+1)) := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0<2*m) (by linarith : 2*m<Real.pi)
  have hcos : Real.cos (2*m)-1 ≠ 0 := by
    intro h
    have hid := Real.sin_sq_add_cos_sq (2*m)
    have hc : Real.cos (2*m)=1 := sub_eq_zero.mp h
    rw [hc] at hid
    nlinarith [sq_pos_of_pos hsin]
  have hmem := properPolynomial_mem
    (fun u : TransformDomain m => (Real.cos (2*u.val):ℂ)) 1 (Real.cos (2*m):ℂ)
    (fun u => by
      have hu : |u.val| < Real.pi/2 := by linarith [u.property,abs_nonneg m]
      simpa only [Complex.ofReal_add,Complex.ofReal_one,add_comm] using
        Complex.ofReal_ne_zero.mpr (reciprocalCosine_den_ne_zero hu))
    (fun u => by simpa only [Complex.ofReal_add] using
      Complex.ofReal_ne_zero.mpr (cosine_sum_pos u.property).ne')
    (by simpa only [Complex.ofReal_sub,Complex.ofReal_one] using Complex.ofReal_ne_zero.mpr hcos)
    (zTransformLinear m N).range N (N+1)
    (firstPole_mem_range m N) (secondPole_mem_range hm hm' N) p (by omega)
  obtain ⟨f,hf⟩ := hmem
  refine ⟨f.val,f.property,?_⟩
  intro u
  exact congrFun hf u

end CriticalHoneycomb.FiniteFunctional.Analytic

end

end OAI
