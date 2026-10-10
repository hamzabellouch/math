import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.CenteredLineMoment

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

lemma fallingMoment_le_two_pow {m h v : ℕ} (hm : 0 < m)
    (hl : (h:ℝ)+v ≤ (m:ℝ)/2) : fallingMoment m h v ≤ (2:ℝ)^v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hmr : (0:ℝ) < m := Nat.cast_pos.mpr hm
    have hv : h+v < m := by exact_mod_cast (show (h:ℝ)+v < m by push_cast at hl; linarith)
    have hi := ih (by push_cast at hl; linarith)
    have hn := (fallingMoment_pos hm (Nat.le_of_lt hv)).le
    have hn' := (fallingMoment_pos hm (by exact_mod_cast (show (h:ℝ)+(v+1) ≤ m by push_cast at hl; linarith))).le
    have hs := fallingMoment_succ hv
    have hd : (m:ℝ)/2 ≤ (m:ℝ)-h-v := by push_cast at hl; linarith
    have ha := mul_le_mul_of_nonneg_right hd hn'
    have hb := mul_le_mul_of_nonneg_left hi hmr.le
    rw [pow_succ]
    nlinarith

lemma light_real_lt {m h n : ℕ} {η : ℝ} (hm : 0 < m) (hη : η ≤ 1/4)
    (hl : (h:ℝ)+n ≤ m*η) : h+n < m := by
  have hp : (0:ℝ) < m := Nat.cast_pos.mpr hm
  exact_mod_cast (show (h:ℝ)+n < m by nlinarith)

theorem centeredLineMoment_light {m h u v : ℕ} {η : ℝ}
    (hm : 0 < m) (hη0 : 0 ≤ η) (hη : η ≤ 1/4)
    (hl : (h:ℝ)+u+v ≤ m*η) :
    0 ≤ centeredLineMoment m h u v ∧
      centeredLineMoment m h u v ≤ (2:ℝ)^v * (4*Real.sqrt η)^u := by
  have hmr : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hr0 : 0 ≤ 4*Real.sqrt η := by positivity
  have hr2 : 4*Real.sqrt η ≤ 2 := by
    have hs := Real.sq_sqrt hη0
    have hs0 := Real.sqrt_nonneg η
    nlinarith
  have hrsq : (4*Real.sqrt η)^2 = 16*η := by rw [mul_pow,Real.sq_sqrt hη0]; norm_num
  have hetr : η ≤ 4*Real.sqrt η := by nlinarith [Real.sq_sqrt hη0,Real.sqrt_nonneg η]
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero =>
      rw [centeredLineMoment_zero,pow_zero,mul_one]
      have hv : h+v ≤ m := Nat.le_of_lt (light_real_lt hm hη (by simpa using hl))
      exact ⟨(fallingMoment_pos hm hv).le,fallingMoment_le_two_pow hm (by nlinarith)⟩
    | succ u =>
      cases u with
      | zero =>
        have hb := fallingMoment_le_two_pow hm (show (h:ℝ)+v ≤ m/2 by push_cast at hl; nlinarith)
        have hv : h+v < m := light_real_lt hm hη (by push_cast at hl; linarith)
        have hbn := (fallingMoment_pos hm (Nat.le_of_lt hv)).le
        have he := centeredLineMoment_one hv
        have hd : 0 < (m:ℝ)-h-v := by
          have hv' : (h:ℝ)+v < m := by exact_mod_cast hv
          linarith
        have hp : 0 ≤ centeredLineMoment m h 1 v := by
          apply nonneg_of_mul_nonneg_right (by rw [he]; positivity) hd
        refine ⟨hp,?_⟩
        rw [pow_one]
        have ha : (m:ℝ)/2 ≤ (m:ℝ)-h-v := by push_cast at hl; nlinarith
        have hc : (h:ℝ)+v ≤ m*η := by push_cast at hl; linarith
        have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ (h:ℝ)+v by positivity)
        have hc' := mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ 2^v by positivity)
        have ha' := mul_le_mul_of_nonneg_right ha hp
        have hr : 2*η ≤ 4*Real.sqrt η := by nlinarith [Real.sq_sqrt hη0,Real.sqrt_nonneg η]
        have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ (m:ℝ)*(2:ℝ)^v by positivity)
        nlinarith
      | succ u =>
        have hu1 := ih (u+1) (by omega) (by push_cast at hl ⊢; linarith)
        have hu0 := ih u (by omega) (by push_cast at hl ⊢; linarith)
        have hv : h+v+u+1 < m := by
          have hh : (h:ℝ)+(v+u+1) ≤ m*η := by push_cast at hl; linarith
          have ht := light_real_lt (h := h) (n := v+u+1) hm hη (by simpa only [Nat.cast_add,Nat.cast_one] using hh)
          omega
        have he := centeredLineMoment_recurrence hv
        have hd : 0 < (m:ℝ)-h-v-u-1 := by
          have hv' : (h:ℝ)+v+u+1 < m := by exact_mod_cast hv
          linarith
        have hp : 0 ≤ centeredLineMoment m h (u+2) v := by
          apply nonneg_of_mul_nonneg_right (by
            rw [he]
            exact add_nonneg (mul_nonneg (by positivity) hu1.1)
              (mul_nonneg (by positivity) hu0.1)) hd
        refine ⟨hp,?_⟩
        have ha : (m:ℝ)/2 ≤ (m:ℝ)-h-v-u-1 := by push_cast at hl; nlinarith
        have hc : (h:ℝ)+v+2*u+2 ≤ 2*m*η := by
          have hhv : (0:ℝ) ≤ h+v := by positivity
          push_cast at hl
          linarith
        have hc0 : 0 ≤ (h:ℝ)+v+2*u+2 := by positivity
        have hb : (u:ℝ)+1 ≤ m*η := by
          have hhv : (0:ℝ) ≤ h+v := by positivity
          push_cast at hl
          linarith
        have ha' := mul_le_mul_of_nonneg_right ha hp
        have hc' := mul_le_mul hc hu1.2 hu1.1 (by positivity : 0 ≤ 2*(m:ℝ)*η)
        have hb' := mul_le_mul hb hu0.2 hu0.1 (by positivity : 0 ≤ (m:ℝ)*η)
        have hr : 4*η*(4*Real.sqrt η)+2*η ≤ (4*Real.sqrt η)^2 := by
          rw [hrsq]
          nlinarith
        have hr' := mul_le_mul_of_nonneg_left hr
          (show 0 ≤ (m:ℝ)/2*((2:ℝ)^v*(4*Real.sqrt η)^u) by positivity)
        simp only [pow_succ] at hc' ⊢
        nlinarith

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

variable {L : Type*} [Fintype L]

def multilineMoment (m h : L → ℕ) : MvPolynomial L ℝ →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials L ℝ).constr ℝ
    (fun n => ∏ l, fallingMoment (m l) (h l) (n l))

lemma multilineMoment_monomial (m h : L → ℕ) (n : L →₀ ℕ) :
    multilineMoment m h (MvPolynomial.monomial n 1) =
      ∏ l, fallingMoment (m l) (h l) (n l) := by
  exact (MvPolynomial.basisMonomials L ℝ).constr_basis ℝ _ n

lemma multiline_prod_X (n : L → ℕ) :
    (∏ l, (MvPolynomial.X l : MvPolynomial L ℝ) ^ n l) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm n) 1 := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  change (∏ l, MvPolynomial.X l ^ (Finsupp.equivFunOnFinite.symm n) l) = _
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro l _ hl
  have hz := Finsupp.notMem_support_iff.mp hl
  change n l = 0 at hz
  change (MvPolynomial.X l : MvPolynomial L ℝ)^n l = 1
  rw [hz,pow_zero]

theorem multilineMoment_factor (m h : L → ℕ) (P : L → Polynomial ℝ) :
    multilineMoment m h (∏ l, Polynomial.aeval (MvPolynomial.X l) (P l)) =
      ∏ l, lineMoment (m l) (h l) (P l) := by
  let f : MultilinearMap ℝ (fun _ : L => Polynomial ℝ) ℝ :=
    (multilineMoment m h).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℝ L (MvPolynomial L ℝ)).compLinearMap
        (fun l => (Polynomial.aeval (MvPolynomial.X l)).toLinearMap))
  let g : MultilinearMap ℝ (fun _ : L => Polynomial ℝ) ℝ :=
    (MultilinearMap.mkPiAlgebra ℝ L ℝ).compLinearMap (fun l => lineMoment (m l) (h l))
  have he : f = g := by
    apply Module.Basis.ext_multilinear (fun _ : L => Polynomial.basisMonomials ℝ)
    intro n
    change multilineMoment m h (∏ l, Polynomial.aeval (MvPolynomial.X l)
      (Polynomial.basisMonomials ℝ (n l))) =
        ∏ l, lineMoment (m l) (h l) (Polynomial.basisMonomials ℝ (n l))
    simp only [Polynomial.coe_basisMonomials,Polynomial.aeval_monomial,map_one,one_mul,
      lineMoment_monomial]
    rw [multiline_prod_X,multilineMoment_monomial]
    rfl
  exact congrArg (fun a => a P) he

lemma multilineMoment_centered (m h u v : L → ℕ) :
    multilineMoment m h (∏ l, (MvPolynomial.X l : MvPolynomial L ℝ)^v l *
      (MvPolynomial.X l-1)^u l) =
        ∏ l, centeredLineMoment (m l) (h l) (u l) (v l) := by
  change multilineMoment m h _ = ∏ l, lineMoment (m l) (h l)
    (Polynomial.X^v l * (Polynomial.X-1)^u l)
  rw [← multilineMoment_factor]
  apply congrArg (multilineMoment m h)
  apply Finset.prod_congr rfl
  intro l _
  rw [map_mul,map_pow,map_pow,map_sub,map_one,Polynomial.aeval_X]

end BinaryCoordinateSweeps.Sparse

end

end OAI
