import OAI.Geometry.PolarProducts.GradientLinking

namespace OAI

universe u89 u90 u91 u92 u93 u94 u95 u96 u97 u98 u99

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
abbrev Time := AddCircle (1 : ℝ)
abbrev μ : Measure Time := AddCircle.haarAddCircle

def eval {ι : Type u89} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) (t : Time) : ℂ :=
  ∑ i, a i * fourier (k i) t

 theorem continuous_eval {ι : Type u90} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    Continuous (eval k a) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (fourier (k i)).continuous)

 theorem integral_fourier (k : ℤ) :
    (∫ t : Time, fourier k t ∂μ) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    eq_comm (a := (0 : ℤ))] using h

 theorem integrable_continuous {G : Type u91} [NormedAddCommGroup G]
    {f : Time → G} (hf : Continuous f) : Integrable f μ := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ

 theorem integral_conj_fourier_mul (k l : ℤ) :
    (∫ t : Time, conj (fourier k t) * fourier l t ∂μ) = if k = l then 1 else 0 := by
  simp_rw [← fourier_neg, ← fourier_add]
  rw [integral_fourier]
  simp only [neg_add_eq_zero]

 theorem integral_conj_eval_mul {ι : Type u92} {κ : Type u93} [Fintype ι] [Fintype κ]
    (k : ι → ℤ) (l : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) :
    (∫ t : Time, conj (eval k a t) * eval l b t ∂μ) =
      ∑ i, ∑ j, if k i = l j then conj (a i) * b j else 0 := by
  classical
  have he (t : Time) : conj (eval k a t) * eval l b t =
      ∑ i, ∑ j, conj (a i)*conj (fourier (k i) t)*(b j*fourier (l j) t) := by
    change conj (∑ i, a i*fourier (k i) t) * eval l b t = _
    rw [map_sum, Finset.sum_mul]
    simp only [map_mul, eval, Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      simp_rw [show ∀ t : Time, conj (a i) * conj (fourier (k i) t) *
          (b j * fourier (l j) t) =
          (conj (a i)*b j) * (conj (fourier (k i) t)*fourier (l j) t) by intro t; ring]
      rw [integral_const_mul, integral_conj_fourier_mul]
      split_ifs <;> simp
    · intro j _
      exact integrable_continuous ((continuous_const.mul ((fourier (k i)).continuous.star)).mul
        (continuous_const.mul (fourier (l j)).continuous))
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact integrable_continuous ((continuous_const.mul ((fourier (k i)).continuous.star)).mul
      (continuous_const.mul (fourier (l j)).continuous))

 theorem norm_sq_re (z : ℂ) : ‖z‖^2 = (conj z*z).re := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

 theorem integral_norm_sq {ι : Type u94} [Fintype ι] (k : ι → ℤ) (hk : Function.Injective k)
    (a : ι → ℂ) : (∫ t : Time, ‖eval k a t‖^2 ∂μ) = ∑ i, ‖a i‖^2 := by
  classical
  simp_rw [norm_sq_re]
  have hI : Integrable (fun t : Time => conj (eval k a t) * eval k a t) μ :=
    integrable_continuous ((continuous_eval k a).star.mul (continuous_eval k a))
  change (∫ t : Time, RCLike.re (conj (eval k a t)*eval k a t) ∂μ) = _
  rw [integral_re hI, integral_conj_eval_mul]
  simp only [hk.eq_iff]
  simp

 theorem coe_integral_norm_fourth {ι : Type u95} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    (((∫ t : Time, ‖eval k a t‖^4 ∂μ) : ℝ) : ℂ) =
      ∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0 := by
  let k' : ι × ι → ℤ := fun p => k p.1+k p.2
  let a' : ι × ι → ℂ := fun p => a p.1*a p.2
  have heval (t : Time) : eval k' a' t = eval k a t * eval k a t := by
    simp only [eval, k', a', Fintype.sum_prod_type, fourier_add, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hintegrand (t : Time) : (↑(‖eval k a t‖^4) : ℂ) =
      conj (eval k' a' t)*eval k' a' t := by
    rw [heval, map_mul, mul_mul_mul_comm, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.sq_norm]
    push_cast
    ring
  rw [← integral_complex_ofReal]
  simp_rw [hintegrand]
  exact integral_conj_eval_mul k' k' a' a'

end
end FourierPolynomial

namespace WeightedSchur
noncomputable section
open Finset

 theorem two_mul_le_weighted {w v : ℝ} (hw : 0 < w) (hv : 0 < v) (x y : ℝ) :
    2*x*y ≤ w*x^2/v + v*y^2/w := by
  rw [div_add_div _ _ hv.ne' hw.ne', le_div_iff₀ (mul_pos hv hw)]
  nlinarith [sq_nonneg (w*x-v*y)]

 theorem sum_le {ι : Type u96} [Fintype ι] (r : ι → ι → Prop) [DecidableRel r]
    (hr : ∀ {i j}, r i j → r j i) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (x : ι → ℝ)
    {C : ℝ} (hrow : ∀ i, (∑ j, if r i j then 1/w j else 0) ≤ C) :
    (∑ i, ∑ j, if r i j then x i*x j else 0) ≤ C * ∑ i, w i*x i^2 := by
  have hp (i j : ι) : 2*(if r i j then x i*x j else 0) ≤
      (if r i j then w i*x i^2/w j else 0) +
      (if r j i then w j*x j^2/w i else 0) := by
    by_cases hij : r i j
    · simp only [ite_eq_left hij, ite_eq_left (hr hij)]
      simpa only [mul_assoc] using two_mul_le_weighted (hw i) (hw j) (x i) (x j)
    · have hji : ¬r j i := fun h => hij (hr h)
      simp only [ite_eq_right hij, ite_eq_right hji, mul_zero, add_zero, le_refl]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) => hp i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hcomm : (∑ i : ι, ∑ j : ι, if r j i then w j*x j^2/w i else 0) =
      ∑ i : ι, ∑ j : ι, if r i j then w i*x i^2/w j else 0 := Finset.sum_comm
  rw [hcomm] at hs
  have hh : (∑ i : ι, ∑ j : ι, if r i j then w i*x i^2/w j else 0) ≤
      C * ∑ i, w i*x i^2 := by
    calc
      _ = ∑ i, w i*x i^2 * (∑ j, if r i j then 1/w j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ ≤ ∑ i, w i*x i^2*C := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg (hw i).le (sq_nonneg _)))
      _ = _ := by rw [← Finset.sum_mul]; ring
  linarith

 theorem reciprocal_pair_rows {ι : Type u97} [Fintype ι] (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (p : ι × ι) :
    (∑ q : ι × ι, if k p.1+k p.2 = k q.1+k q.2 then
      1 / ((k q.1 : ℝ)*(k q.2 : ℝ)) else 0) ≤ 1 := by
  classical
  let m := k p.1+k p.2
  have hm : 2 ≤ m := by dsimp [m]; have := hk0 p.1; have := hk0 p.2; omega
  let Q := univ.filter (fun q : ι × ι => k q.1+k q.2 = m)
  have hQ (q : ι × ι) : q ∈ Q ↔ k q.1+k q.2 = m := by simp [Q]
  have hmaps : Set.MapsTo (fun q : ι × ι => k q.1) (↑Q : Set (ι × ι))
      (↑(Icc 1 (m-1)) : Set ℕ) := by
    intro q hq
    have he := (hQ q).mp hq
    have h0 := hk0 q.1
    have h1 := hk0 q.2
    simp only [mem_coe, mem_Icc]
    omega
  have hinj : Set.InjOn (fun q : ι × ι => k q.1) (↑Q : Set (ι × ι)) := by
    intro q hq z hz he
    change k q.1 = k z.1 at he
    have hq' := (hQ q).mp hq
    have hz' := (hQ z).mp hz
    apply Prod.ext (hk he)
    apply hk
    omega
  have hc : Q.card ≤ m-1 := by
    have hc' := Finset.card_le_card_of_injOn (fun q : ι × ι => k q.1) hmaps hinj
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc'
  have hd : 0 < (m : ℝ)-1 := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hterm (q : ι × ι) (hq : q ∈ Q) :
      1/((k q.1 : ℝ)*(k q.2 : ℝ)) ≤ 1/((m : ℝ)-1) := by
    apply one_div_le_one_div_of_le hd
    have h0 : 1 ≤ (k q.1 : ℝ) := by exact_mod_cast (show 1 ≤ k q.1 from hk0 q.1)
    have h1 : 1 ≤ (k q.2 : ℝ) := by exact_mod_cast (show 1 ≤ k q.2 from hk0 q.2)
    have he : (k q.1 : ℝ)+(k q.2 : ℝ) = m := by exact_mod_cast (hQ q).mp hq
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  calc
    _ = ∑ q ∈ Q, 1/((k q.1 : ℝ)*(k q.2 : ℝ)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      simp only [m, eq_comm (a := k q.1+k q.2)]
    _ ≤ ∑ _q ∈ Q, 1/((m : ℝ)-1) := Finset.sum_le_sum hterm
    _ = (Q.card : ℝ)/((m : ℝ)-1) := by simp [div_eq_mul_inv]
    _ ≤ 1 := by
      rw [div_le_one hd]
      have hcR : (Q.card : ℝ) ≤ (m-1 : ℕ) := by exact_mod_cast hc
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hcR
      exact hcR

end
end WeightedSchur

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

 theorem integral_norm_fourth_le_pairs {ι : Type u98} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    (∫ t : Time, ‖eval k a t‖^4 ∂μ) ≤
      ∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then
          (‖a p.1‖*‖a p.2‖)*(‖a q.1‖*‖a q.2‖) else 0 := by
  classical
  have hI : 0 ≤ ∫ t : Time, ‖eval k a t‖^4 ∂μ := integral_nonneg (fun _ => by positivity)
  calc
    _ = ‖(((∫ t : Time, ‖eval k a t‖^4 ∂μ) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI]
    _ = ‖∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0‖ :=
      congrArg norm (coe_integral_norm_fourth k a)
    _ ≤ ∑ p : ι × ι, ∑ q : ι × ι,
        ‖if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp only [norm_mul, Complex.norm_conj, norm_zero]

 theorem positive_L4 {ι : Type u99} [Fintype ι] (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (a : ι → ℂ) :
    (∫ t : Time, ‖eval (fun i => (k i : ℤ)) a t‖^4 ∂μ) ≤
      (∑ i, (k i : ℝ)*‖a i‖^2)^2 := by
  classical
  have hrows := WeightedSchur.reciprocal_pair_rows k hk hk0
  let w : ι × ι → ℝ := fun p => (k p.1 : ℝ)*(k p.2 : ℝ)
  have hw (p : ι × ι) : 0 < w p := by
    exact mul_pos (by exact_mod_cast hk0 p.1) (by exact_mod_cast hk0 p.2)
  have hS := WeightedSchur.sum_le
    (fun p q : ι × ι => k p.1+k p.2 = k q.1+k q.2)
    (fun h => h.symm) w hw (fun p => ‖a p.1‖*‖a p.2‖) hrows
  have hpair := integral_norm_fourth_le_pairs (fun i => (k i : ℤ)) a
  simp only [← Nat.cast_add, Int.natCast_inj] at hpair
  apply hpair.trans
  apply (hS.trans_eq _)
  simp only [one_mul, Fintype.sum_prod_type, w]
  calc
    _ = ∑ i, ∑ j, ((k i : ℝ)*‖a i‖^2)*((k j : ℝ)*‖a j‖^2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.sum_mul_sum]; ring

end
end FourierPolynomial

end NonsqueezingInline

end OAI
