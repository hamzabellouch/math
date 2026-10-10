import OAI.NumberTheory.CubicMoment.Estimates.CoprimeDispersionPoisson
import OAI.NumberTheory.CubicMoment.Estimates.CubeUniformError
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments

namespace OAI

/-! The uncorrected prime variance retains its diagonal. This is the
finite algebra and cube estimate needed at the three-prime transition. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem prime_variance_split (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (β : Eisenstein → ℂ) (u : ℝ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) :
    smoothedDispersionVariance S β u V A =
      (∑ p ∈ S, dispersionAmplitude β u p*star (dispersionAmplitude β u p)*
        primaryCharacterGram p p V A) + coprimeDispersionGram S β u V A := by
  rw [smoothedDispersionVariance_gram S (fun p hp => (hS p hp).1) β u V hV hV' hA]
  unfold coprimeDispersionGram
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.add_sum_erase S _ hp]
  congr 1
  rw [← Finset.add_sum_erase S _ hp]
  have hself : ¬IsCoprime p p := fun h => (hS p hp).2.not_isUnit (isCoprime_self.mp h)
  simp only [hself,ite_false,zero_add]
  apply Finset.sum_congr rfl
  intro q hq
  rw [ite_eq_left (primaryPrimes_isCoprime (hS p hp)
    (hS q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq).symm)]

theorem primary_coprime_mass_bound (V : ℝ → ℂ) {A R M : ℝ}
    (hA : 0 < A) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hV : ∀ x, ‖V x‖ ≤ M) (hcut : ∀ x, R < x → V x = 0) (p : Eisenstein) :
    ‖∑' a : Eisenstein, if primary a ∧ IsCoprime p a then V (norm a/A) else 0‖ ≤
      18*R*A*M := by
  have he : (∑' a : Eisenstein, if primary a ∧ IsCoprime p a then V (norm a/A) else 0) =
      ∑ a ∈ primaryElementBall (R*A),
        if primary a ∧ IsCoprime p a then V (norm a/A) else 0 := by
    apply tsum_eq_sum
    intro a ha
    by_cases hp : primary a
    · have hn : R < norm a/A := by
        apply (lt_div_iff₀ hA).mpr
        exact lt_of_not_ge (fun h => ha (mem_primaryElementBall.mpr ⟨hp,h⟩))
      simp only [hcut _ hn,ite_self]
    · simp only [hp,false_and,ite_false]
  rw [he]
  calc
    _ ≤ ∑ a ∈ primaryElementBall (R*A),
        ‖if primary a ∧ IsCoprime p a then V (norm a/A) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ primaryElementBall (R*A), M := Finset.sum_le_sum (fun a _ => by
      split_ifs
      · exact hV _
      · simpa only [norm_zero] using hM)
    _ = ((primaryElementBall (R*A)).card:ℝ)*M := by simp
    _ ≤ (18*(R*A))*M := mul_le_mul_of_nonneg_right
      (primaryElementBall_card_le (mul_nonneg hR hA.le)) hM
    _ = _ := by ring

theorem prime_dispersion_diagonal_bound (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (β : Eisenstein → ℂ) (u : ℝ)
    (V : ℝ → ℂ) {A R M : ℝ} (hA : 0 < A) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hV : ∀ x, ‖V x‖ ≤ M) (hcut : ∀ x, R < x → V x = 0) :
    ‖∑ p ∈ S, dispersionAmplitude β u p*star (dispersionAmplitude β u p)*
        primaryCharacterGram p p V A‖ ≤ (18*R*M)*A*∑ p ∈ S, ‖β p‖^2 := by
  rw [dispersion_diagonal S (fun p hp => (hS p hp).1)
    (fun p hp => (hS p hp).2.squarefree) β u V A]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ S, ‖β p‖^2*(18*R*A*M) := Finset.sum_le_sum (fun p _ => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (primary_coprime_mass_bound V hA hR hM hV hcut p) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem coprimeCubeMainTerm_norm_bound (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hN : ∀ p ∈ S, B ≤ norm p) :
    ‖coprimeCubeMainTerm S β u V A‖ ≤
      (A^(2/3:ℝ)*B^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖)*
        (∑ p ∈ S, ‖β p‖)^2 := by
  unfold coprimeCubeMainTerm
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ S, ∑ q ∈ S,
        ‖β p‖*‖β q‖*(A^(2/3:ℝ)*B^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖) := by
      apply Finset.sum_le_sum
      intro p hp
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      split_ifs
      · have hrad : 0 ≤ A^(2/3:ℝ)*(norm (q*p))^(-(1/6:ℝ))/9 :=
          div_nonneg (mul_nonneg (Real.rpow_nonneg hA _)
            (Real.rpow_nonneg (norm_nonneg _) _)) (by norm_num)
        simp only [norm_mul,norm_star,norm_normTwist,mul_one,Complex.norm_real,
          Real.norm_of_nonneg hrad]
        have hh := (cube_pair_norm_bounds hB (hN p hp) (hN q hq)).2
        calc
          _ ≤ ‖β p‖*‖β q‖*(A^(2/3:ℝ)*B^(-(1/3:ℝ))/9)*‖cubeProfileIntegral V‖ := by
            gcongr
          _ = _ := by ring
      · simp only [norm_zero]; positivity
    _ = _ := by
      simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring

lemma cube_transition_scale {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B^2) :
    A/B ≤ A^(2/3:ℝ)*B^(-(1/3:ℝ)) := by
  have hh := Real.rpow_le_rpow hA.le hAB (show (0:ℝ) ≤ 1/3 by norm_num)
  rw [← Real.rpow_natCast B 2,← Real.rpow_mul hB.le] at hh
  have ha : A = A^(2/3:ℝ)*A^(1/3:ℝ) := by
    rw [← Real.rpow_add hA]; norm_num
  calc
    A/B = A^(2/3:ℝ)*A^(1/3:ℝ)/B := by rw [← ha]
    _ ≤ A^(2/3:ℝ)*B^(2/3:ℝ)/B := by gcongr; norm_num at hh ⊢; exact hh
    _ = _ := by rw [div_eq_mul_inv,← Real.rpow_neg_one B,
      mul_assoc,← Real.rpow_add hB]; norm_num

end CubicFirstMoment

end

end OAI
