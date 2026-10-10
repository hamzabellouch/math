import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators

namespace CoulombAtom

lemma weighted_sum_integral_cauchy {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) (w f g : ∀ i, X i → ℝ)
    (hw : ∀ i x, 0 ≤ w i x)
    (hf : ∀ i, Integrable (fun x => f i x^2*w i x) (μ i))
    (hg : ∀ i, Integrable (fun x => g i x^2*w i x) (μ i))
    (hfg : ∀ i, Integrable (fun x => f i x*g i x*w i x) (μ i)) :
    (∑ i, ∫ x, f i x*g i x*w i x ∂μ i) ≤
      Real.sqrt (∑ i, ∫ x, f i x^2*w i x ∂μ i)*
        Real.sqrt (∑ i, ∫ x, g i x^2*w i x ∂μ i) := by
  let A := ∑ i, ∫ x, f i x^2*w i x ∂μ i
  let B := ∑ i, ∫ x, g i x^2*w i x ∂μ i
  let C := ∑ i, ∫ x, f i x*g i x*w i x ∂μ i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw i x)))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw i x)))
  have hq (r : ℝ) : 0 ≤ A*(r*r)+(-2*C)*r+B := by
    have he (i : ι) : (∫ x, (r*f i x-g i x)^2*w i x ∂μ i) =
        r^2*(∫ x, f i x^2*w i x ∂μ i)-
          (2*r)*(∫ x, f i x*g i x*w i x ∂μ i)+∫ x, g i x^2*w i x ∂μ i := by
      have hp (x : X i) : (r*f i x-g i x)^2*w i x =
          r^2*(f i x^2*w i x)-(2*r)*(f i x*g i x*w i x)+(g i x^2*w i x) := by ring
      simp_rw [hp]
      have hadd := integral_add (((hf i).const_mul (r^2)).sub ((hfg i).const_mul (2*r))) (hg i)
      have hsub := integral_sub ((hf i).const_mul (r^2)) ((hfg i).const_mul (2*r))
      simp only [Pi.sub_apply,integral_const_mul] at hadd hsub
      rw [hadd,hsub]
    have hn : 0 ≤ ∑ i, ∫ x, (r*f i x-g i x)^2*w i x ∂μ i :=
      Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw i x)))
    simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hn
    dsimp only [A,B,C]
    nlinarith
  have hd := discrim_le_zero hq
  have hsq : C^2 ≤ A*B := by
    unfold discrim at hd
    nlinarith
  change C ≤ Real.sqrt A*Real.sqrt B
  rw [←Real.sqrt_mul hA]
  nlinarith [Real.sq_sqrt (mul_nonneg hA hB),Real.sqrt_nonneg (A*B)]

end CoulombAtom

end

end OAI
