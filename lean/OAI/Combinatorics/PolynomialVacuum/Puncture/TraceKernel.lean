import OAI.Combinatorics.PolynomialVacuum.Puncture.GramJensen

namespace OAI

namespace PolynomialVacuumCylinder
open MeasureTheory Matrix

 

noncomputable def denominatorReferenceKernel (n : ℕ) (p : ℝ) : ℝ :=
  dotProduct (fun j : Fin n=>p^(2*j.val))
    ((denominatorReferenceMatrix n)⁻¹ *ᵥ (fun j : Fin n=>p^(2*j.val)))

theorem denominatorReferenceKernel_nonneg (n : ℕ) (p : ℝ) :
    0≤denominatorReferenceKernel n p := by
  have h := (denominatorReferenceMatrix_posDef n).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun j : Fin n=>p^(2*j.val))
  simpa only [Pi.star_apply,star_trivial,denominatorReferenceKernel] using h

private theorem denominator_kernel_expand (n : ℕ) (p : ℝ) :
    denominatorReferenceKernel n p*denominatorReferenceWeight p*denominatorCorrection p =
      ∑ j : Fin n,∑ k : Fin n,(denominatorReferenceMatrix n)⁻¹ j k *
        (p^(2*k.val+2*j.val)*denominatorReferenceWeight p*denominatorCorrection p) := by
  unfold denominatorReferenceKernel
  simp only [dotProduct,mulVec]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

 

theorem denominatorCorrectionTrace_integral (n : ℕ) :
    denominatorCorrectionTrace n =
      ∫ p : ℝ,denominatorReferenceKernel n p*
        denominatorReferenceWeight p*denominatorCorrection p := by
  have hint (j k : Fin n) : Integrable (fun p : ℝ=>
      (denominatorReferenceMatrix n)⁻¹ j k *
        (p^(2*k.val+2*j.val)*denominatorReferenceWeight p*denominatorCorrection p)) :=
    (denominatorCorrectionMatrix_entry_integrable n k j).const_mul _
  rw [show (fun p : ℝ=>denominatorReferenceKernel n p*denominatorReferenceWeight p*
    denominatorCorrection p)=(fun p : ℝ=>∑ j : Fin n,∑ k : Fin n,
    (denominatorReferenceMatrix n)⁻¹ j k *
      (p^(2*k.val+2*j.val)*denominatorReferenceWeight p*denominatorCorrection p)) from
      funext (denominator_kernel_expand n)]
  rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun k _=>hint j k))]
  simp_rw [integral_finsetSum _ (fun k _=>hint _ k),integral_const_mul]
  rfl

end PolynomialVacuumCylinder

end OAI
