import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearCauchy

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def priorMaxAtom (ν : κ → ℝ) : ℝ :=
  ((Finset.univ.sup (fun q => (ν q).toNNReal) : NNReal) : ℝ)

theorem prior_le_maxAtom (ν : κ → ℝ) (hν : ∀ q, 0 ≤ ν q) (q : κ) :
    ν q ≤ priorMaxAtom ν := by
  have h := Finset.le_sup (f := fun q => (ν q).toNNReal) (Finset.mem_univ q)
  have hc : ((ν q).toNNReal : ℝ) ≤ priorMaxAtom ν := by exact_mod_cast h
  simpa only [Real.coe_toNNReal _ (hν q)] using hc

omit [Fintype κ] in
theorem oneSidedGram_diagonal (b : ι → ℝ) (F : ι → κ → ℂ) (q : κ) :
    oneSidedGram b F q q = ((∑ n, b n * ‖F n q‖^2 : ℝ) : ℂ) := by
  simp only [oneSidedGram, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.normSq_eq_norm_sq]

omit [Fintype κ] in
theorem norm_oneSidedGram_diagonal (b : ι → ℝ) (hb : ∀ n, 0 ≤ b n)
    (F : ι → κ → ℂ) (q : κ) :
    ‖oneSidedGram b F q q‖ = ∑ n, b n * ‖F n q‖^2 := by
  rw [oneSidedGram_diagonal, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg (fun n _ => mul_nonneg (hb n) (sq_nonneg _)))

theorem oneSided_energy_le_diagonal_cross (b : ι → ℝ) (ν : κ → ℝ)
    (V : κ → ℂ) (F : ι → κ → ℂ)
    (hb : ∀ n, 0 ≤ b n) (hν : ∀ q, 0 ≤ ν q) (hV : ∀ q, ‖V q‖ ≤ 1) :
    (∑ n, b n * ‖∑ q, (ν q : ℂ) * V q * F n q‖^2) ≤
      priorMaxAtom ν * (∑ q, ν q * ∑ n, b n * ‖F n q‖^2) +
        ∑ q, ∑ q', if q = q' then 0 else ν q * ν q' * ‖oneSidedGram b F q q'‖ := by
  classical
  have hcoeff (q : κ) : ‖(ν q : ℂ) * V q‖ ≤ ν q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν q)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hV q) (hν q)
  have hsplit (q : κ) :
      (∑ q', ν q * ν q' * ‖oneSidedGram b F q q'‖) =
        ν q^2 * (∑ n, b n * ‖F n q‖^2) +
          ∑ q', if q = q' then 0 else ν q * ν q' * ‖oneSidedGram b F q q'‖ := by
    calc
      _ = ∑ q', ((if q = q' then ν q^2 * (∑ n, b n * ‖F n q‖^2) else 0) +
          (if q = q' then 0 else ν q * ν q' * ‖oneSidedGram b F q q'‖)) := by
        apply Finset.sum_congr rfl
        intro q' hq'
        by_cases hqq : q = q'
        · subst q'
          simp [norm_oneSidedGram_diagonal b hb F q, pow_two]
        · simp [hqq]
      _ = _ := by simp [Finset.sum_add_distrib]
  calc
    _ = ∑ q, ∑ q', (((ν q : ℂ)*V q) * conj ((ν q' : ℂ)*V q') *
        oneSidedGram b F q q').re := oneSided_energy_expansion b (fun q => (ν q : ℂ)*V q) F
    _ ≤ ∑ q, ∑ q', ν q * ν q' * ‖oneSidedGram b F q q'‖ := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro q' hq'
      apply (Complex.re_le_norm _).trans
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hcoeff q) (hcoeff q') (norm_nonneg _) (hν q)) (norm_nonneg _)
    _ = (∑ q, ν q^2 * (∑ n, b n * ‖F n q‖^2)) +
        ∑ q, ∑ q', if q = q' then 0 else ν q * ν q' * ‖oneSidedGram b F q q'‖ := by
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have hdiag : 0 ≤ ∑ n, b n * ‖F n q‖^2 :=
        Finset.sum_nonneg (fun n _ => mul_nonneg (hb n) (sq_nonneg _))
      have ha := mul_le_mul_of_nonneg_right (prior_le_maxAtom ν hν q) (hν q)
      nlinarith [mul_le_mul_of_nonneg_right ha hdiag]

theorem oneSided_bilinear_gram_bound (μ b : ι → ℝ) (ν : κ → ℝ)
    (U : ι → ℂ) (V : κ → ℂ) (F : ι → κ → ℂ)
    (hμ : ∀ n, 0 ≤ μ n) (hmass : ∑ n, μ n ≤ 1)
    (hmajorant : ∀ n, μ n ≤ b n) (hν : ∀ q, 0 ≤ ν q)
    (hU : ∀ n, ‖U n‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖oneSidedMean μ ν U V F‖^2 ≤
      priorMaxAtom ν * (∑ q, ν q * ∑ n, b n * ‖F n q‖^2) +
        ∑ q, ∑ q', if q = q' then 0 else ν q * ν q' * ‖oneSidedGram b F q q'‖ := by
  exact (oneSided_cauchy_extension μ b U _ hμ hmass hmajorant hU).trans
    (oneSided_energy_le_diagonal_cross b ν V F
      (fun n => (hμ n).trans (hmajorant n)) hν hV)

end Ostmann.Characters

end

end OAI
