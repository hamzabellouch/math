import OAI.Analysis.KadisonKastler.SignedSquareThreshold
import OAI.Analysis.KadisonKastler.FiniteThresholdEstimate

namespace OAI

/-! # Finite outward spectral cuts

Negative thresholds take the lower spectral projection, positive thresholds
take the upper one. Signed-square coordinates make their integrated vector
mass equal to the squared norm of the original finite spectral sum.
-/

namespace KadisonKastler

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

def finiteOutwardProjection (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) : H →L[ℂ] H :=
  if t < 0 then 1-finiteThresholdProjection P (signedSquare ∘ c) t
    else finiteThresholdProjection P (signedSquare ∘ c) t

theorem finiteOutwardProjection_isProjection
    (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (c : ι → ℝ) (t : ℝ) :
    IsStarProjection (finiteOutwardProjection P c t) := by
  unfold finiteOutwardProjection
  split
  · exact (finiteThresholdProjection_isProjection P hP ho _ t).one_sub
  · exact finiteThresholdProjection_isProjection P hP ho _ t

omit [CompleteSpace H] in
theorem finiteOutwardProjection_sum (P : ι → H →L[ℂ] H)
    (htotal : ∑ i, P i=1) (c : ι → ℝ) (t : ℝ) :
    finiteOutwardProjection P c t =
      ∑ i, ((thresholdDifference (signedSquare (c i)) 0 t ^ 2 : ℝ) : ℂ) • P i := by
  simp_rw [← outward_threshold_coefficient]
  by_cases ht : t < 0
  · simp only [finiteOutwardProjection,ht,ite_true,finiteThresholdProjection,Function.comp_apply]
    rw [← htotal,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]
  · simp only [finiteOutwardProjection,ht,ite_false,finiteThresholdProjection,Function.comp_apply]

theorem finiteSpectralSum_norm_sq (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (c : ι → ℝ) (ξ : H) :
    ‖(∑ i, (c i : ℂ) • P i) ξ‖^2 = ∑ i, c i^2*‖P i ξ‖^2 := by
  have hp := orthogonal_projection_vectors P (fun i => (hP i).isSelfAdjoint) ho ξ
  have he := norm_sum_sq_of_pairwise_orthogonal univ
    (fun i => (c i : ℂ) • P i ξ) (by
      intro i _ j _ hij
      rw [inner_smul_left,inner_smul_right,hp hij,mul_zero,mul_zero])
  simpa only [_root_.sum_apply,smul_apply,norm_smul,mul_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs] using he

theorem finiteOutwardProjection_mass (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (htotal : ∑ i, P i=1)
    (c : ι → ℝ) (t : ℝ) (ξ : H) :
    ‖finiteOutwardProjection P c t ξ‖^2 =
      ∑ i, thresholdDifference (signedSquare (c i)) 0 t ^ 2*‖P i ξ‖^2 := by
  rw [finiteOutwardProjection_sum P htotal c t,finiteSpectralSum_norm_sq P hP ho]
  apply sum_congr rfl
  intro i _
  by_cases hx : t < signedSquare (c i) <;> by_cases ht : t < 0 <;>
    simp [thresholdDifference,hx,ht]

theorem finiteOutwardProjection_mass_integrable (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (htotal : ∑ i, P i=1)
    (c : ι → ℝ) (ξ : H) : Integrable (fun t => ‖finiteOutwardProjection P c t ξ‖^2) := by
  simp_rw [finiteOutwardProjection_mass P hP ho htotal c]
  exact integrable_finsetSum _ (fun i _ =>
    (thresholdDifference_sq_integrable (signedSquare (c i)) 0).mul_const _)

theorem finiteOutwardProjection_integral_mass (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (htotal : ∑ i, P i=1)
    (c : ι → ℝ) (ξ : H) :
    (∫ t, ‖finiteOutwardProjection P c t ξ‖^2)=‖(∑ i, (c i : ℂ) • P i) ξ‖^2 := by
  simp_rw [finiteOutwardProjection_mass P hP ho htotal c]
  rw [integral_finsetSum _ (fun i _ =>
    (thresholdDifference_sq_integrable (signedSquare (c i)) 0).mul_const _),
    finiteSpectralSum_norm_sq P hP ho]
  apply sum_congr rfl
  intro i _
  rw [integral_mul_const,integral_outward_threshold_coefficient]

omit [CompleteSpace H] in
theorem finiteOutwardProjection_gap_eq
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (c : ι → ℝ) (d : κ → ℝ) (t : ℝ) (ξ : H) :
    ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2 =
      ‖(finiteThresholdProjection P (signedSquare ∘ c) t-
        finiteThresholdProjection Q (signedSquare ∘ d) t) ξ‖^2 := by
  by_cases ht : t < 0
  · simp only [finiteOutwardProjection,ht,ite_true]
    rw [show (1-finiteThresholdProjection P (signedSquare ∘ c) t)-
      (1-finiteThresholdProjection Q (signedSquare ∘ d) t)=
        -(finiteThresholdProjection P (signedSquare ∘ c) t-
          finiteThresholdProjection Q (signedSquare ∘ d) t) by abel]
    rw [neg_apply,norm_neg]
  · simp only [finiteOutwardProjection,ht,ite_false]

theorem finiteOutwardProjection_integral_gap
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i*P k=0) (hQo : ∀ j l, j ≠ l → Q j*Q l=0)
    (hPt : ∑ i, P i=1) (hQt : ∑ j, Q j=1) (hc : ∀ i j, Commute (P i) (Q j))
    (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∫ t, ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2)=
      ∑ a : ι × κ, ‖(P a.1*Q a.2) ξ‖^2*
        |signedSquare (c a.1)-signedSquare (d a.2)| := by
  simp_rw [finiteOutwardProjection_gap_eq]
  exact finiteThresholdProjection_integrated_energy P Q hP hQ hPo hQo hPt hQt hc _ _ ξ

end

end KadisonKastler

end OAI
