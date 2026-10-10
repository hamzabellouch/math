import OAI.Analysis.KadisonKastler.OutwardSpectralCuts

namespace OAI

/-! # Norm-free energy bounds for outward spectral cuts

The upper estimate uses only the two vector norms and their displacement.
The lower estimate recovers half of the original displacement energy.
-/

namespace KadisonKastler

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

theorem weighted_signedSquare_energy {ι : Type*} (s : Finset ι)
    (x y w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i*|signedSquare (x i)-signedSquare (y i)|)^2 ≤
      (∑ i ∈ s, w i*(x i-y i)^2)*
        (2*((∑ i ∈ s, w i*(x i)^2)+(∑ i ∈ s, w i*(y i)^2))) := by
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => w i*(x i-y i)^2)
    (g := fun i => w i*(|x i|+|y i|)^2)
    (r := fun i => w i*|signedSquare (x i)-signedSquare (y i)|)
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)) (by
      intro i hi
      have hs := (sq_le_sq₀ (abs_nonneg (signedSquare (x i)-signedSquare (y i)))
        (mul_nonneg (abs_nonneg (x i-y i)) (add_nonneg (abs_nonneg _) (abs_nonneg _)))).mpr
          (signedSquare_gap_le (x i) (y i))
      simp only [mul_pow,sq_abs] at hs
      calc
        (w i*|signedSquare (x i)-signedSquare (y i)|)^2 =
            (w i)^2*|signedSquare (x i)-signedSquare (y i)|^2 := mul_pow _ _ _
        _ ≤ (w i)^2*((x i-y i)^2*(|x i|+|y i|)^2) := by
          simpa only [sq_abs] using mul_le_mul_of_nonneg_left hs (sq_nonneg (w i))
        _ = _ := by ring)
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)))
  rw [mul_add,mul_sum,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  have hs : (|x i|+|y i|)^2 ≤ 2*((x i)^2+(y i)^2) := by
    nlinarith [sq_nonneg (|x i|-|y i|),sq_abs (x i),sq_abs (y i)]
  nlinarith [mul_le_mul_of_nonneg_left hs (hw i hi)]

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]
  (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
  (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
  (hPo : ∀ i k, i ≠ k → P i*P k=0) (hQo : ∀ j l, j ≠ l → Q j*Q l=0)
  (hPt : ∑ i, P i=1) (hQt : ∑ j, Q j=1) (hc : ∀ i j, Commute (P i) (Q j))

include hP hQ hPo hQo hPt hQt hc

theorem finiteOutwardProjection_gap_integrable (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    Integrable (fun t => ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2) := by
  simp_rw [finiteOutwardProjection_gap_eq,
    finiteThresholdProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
  exact integrable_finsetSum _ (fun a _ =>
    (thresholdDifference_sq_integrable _ _).const_mul _)

theorem finiteOutwardProjection_integral_lower (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    ‖((∑ i, (c i : ℂ) • P i)-(∑ j, (d j : ℂ) • Q j)) ξ‖^2 ≤
      2*(∫ t, ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2) := by
  rw [finiteOutwardProjection_integral_gap P Q hP hQ hPo hQo hPt hQt hc,
    ← jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc,mul_sum]
  apply sum_le_sum
  intro a _
  nlinarith [mul_le_mul_of_nonneg_left (sq_gap_le_signedSquare (c a.1) (d a.2))
    (sq_nonneg ‖(P a.1*Q a.2) ξ‖)]

theorem finiteOutwardProjection_integral_upper_sq (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∫ t, ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2)^2 ≤
      ‖((∑ i, (c i : ℂ) • P i)-(∑ j, (d j : ℂ) • Q j)) ξ‖^2*
        (2*(‖(∑ i, (c i : ℂ) • P i) ξ‖^2+‖(∑ j, (d j : ℂ) • Q j) ξ‖^2)) := by
  rw [finiteOutwardProjection_integral_gap P Q hP hQ hPo hQo hPt hQt hc]
  have hleft := jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc c (fun _ => 0) ξ
  have hright := jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc (fun _ => 0) d ξ
  simp only [sub_zero,Complex.ofReal_zero,zero_smul,sum_const_zero] at hleft
  simp only [zero_sub,neg_sq,Complex.ofReal_zero,zero_smul,sum_const_zero,neg_apply,norm_neg] at hright
  have he := weighted_signedSquare_energy (univ : Finset (ι × κ))
    (fun a => c a.1) (fun a => d a.2) (fun a => ‖(P a.1*Q a.2) ξ‖^2)
    (fun _ _ => sq_nonneg _)
  rw [jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc,hleft,hright] at he
  exact he

end

end KadisonKastler

end OAI
