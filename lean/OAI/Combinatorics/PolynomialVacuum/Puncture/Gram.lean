import OAI.Combinatorics.PolynomialVacuum.Puncture.Moments

namespace OAI

namespace PolynomialVacuumCylinder
open MeasureTheory Matrix

noncomputable def evenMomentEvaluation {n : ℕ} (u : Fin n → ℝ) (p : ℝ) : ℝ :=
  ∑ j, u j*p^(2*j.val)

private theorem evenMomentEvaluation_expand {n : ℕ} (u : Fin n → ℝ) (p : ℝ) :
    (evenMomentEvaluation u p)^2*denominatorMomentWeight p =
      ∑ j,∑ k,(u j*u k)*(p^(2*j.val+2*k.val)*denominatorMomentWeight p) := by
  unfold evenMomentEvaluation
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

theorem evenMomentEvaluation_integrable {n : ℕ} (u : Fin n → ℝ) :
    Integrable (fun p : ℝ=>(evenMomentEvaluation u p)^2*denominatorMomentWeight p) := by
  have h := integrable_finsetSum Finset.univ (fun j _=>
    integrable_finsetSum Finset.univ (fun k _=>
      (denominator_matrix_entry_integrable n j k).const_mul (u j*u k)))
  simpa only [←evenMomentEvaluation_expand] using h

theorem denominator_gram_identity {n : ℕ} (u : Fin n → ℝ) :
    star u ⬝ᵥ ((denominatorMomentMatrix n)*ᵥ u) =
      ∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorMomentWeight p := by
  simp_rw [evenMomentEvaluation_expand]
  rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun k _=>
    (denominator_matrix_entry_integrable n j k).const_mul (u j*u k)))]
  simp_rw [integral_finsetSum _ (fun k _=>
    (denominator_matrix_entry_integrable n _ k).const_mul (_*u k)),integral_const_mul]
  simp only [dotProduct,mulVec,Pi.star_apply,star_trivial,denominatorMomentMatrix]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem evenMomentEvaluation_nonzero {n : ℕ} (u : Fin n → ℝ) (hu : u≠0) :
    ∃ p : ℝ,evenMomentEvaluation u p≠0 := by
  classical
  let P : Polynomial ℝ := ∑ j : Fin n,Polynomial.monomial (2*j.val) (u j)
  have he (p : ℝ) : P.eval p = evenMomentEvaluation u p := by
    simp [P,evenMomentEvaluation,Polynomial.eval_finsetSum]
  by_contra hn
  push Not at hn
  have hp : P=0 := Polynomial.funext (fun p=>by simpa only [he,Polynomial.eval_zero] using hn p)
  apply hu
  funext j
  have hc := congrArg (fun Q : Polynomial ℝ=>Q.coeff (2*j.val)) hp
  have hcoe : P.coeff (2*j.val)=u j := by
    simp only [P,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      have hkne : 2*k.val≠2*j.val := by intro h; apply hkj; exact Fin.ext (by omega)
      simp [hkne]
    · simp
  simpa only [hcoe,Polynomial.coeff_zero,Pi.zero_apply] using hc

theorem denominator_gram_pos {n : ℕ} (u : Fin n → ℝ) (hu : u≠0) :
    0 < star u ⬝ᵥ ((denominatorMomentMatrix n)*ᵥ u) := by
  rw [denominator_gram_identity]
  rw [integral_pos_iff_support_of_nonneg
    (fun p=>mul_nonneg (sq_nonneg _) (denominatorMomentWeight_pos p).le)
    (evenMomentEvaluation_integrable u)]
  have he : Function.support (fun p=>(evenMomentEvaluation u p)^2*denominatorMomentWeight p)=
      Function.support (evenMomentEvaluation u) := by
    ext p
    change ((evenMomentEvaluation u p)^2*denominatorMomentWeight p≠0) ↔
      evenMomentEvaluation u p≠0
    constructor
    · intro h hz
      apply h
      rw [hz,zero_pow (by norm_num : 2≠0),zero_mul]
    · intro h
      exact mul_ne_zero (pow_ne_zero 2 h) (denominatorMomentWeight_pos p).ne' 
  rw [he]
  have hc : Continuous (evenMomentEvaluation u) := by unfold evenMomentEvaluation; fun_prop
  exact hc.isOpen_support.measure_pos volume (evenMomentEvaluation_nonzero u hu)

 

theorem denominatorMomentMatrix_posDef (n : ℕ) : (denominatorMomentMatrix n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext j k
    simp only [conjTranspose_apply,star_trivial,denominatorMomentMatrix]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [Nat.add_comm]
  · intro u hu
    exact denominator_gram_pos u hu

theorem denominatorMomentMatrix_det_pos (n : ℕ) : 0<(denominatorMomentMatrix n).det :=
  (denominatorMomentMatrix_posDef n).det_pos

end PolynomialVacuumCylinder

end OAI
