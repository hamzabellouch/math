import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeTailHeckeMean
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularWeights

namespace OAI

/-! The actual fixed-angular semiprime window from the derived angular
Hecke height mean, preserving its full product Mellin envelope. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

def semiprimeGaussAngularUnitWindow (r s A B H U X : ℝ) : ℂ :=
  productGaussWindow
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) 1)
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A))
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B))
    ℓ primeProductEnvelope H U X

lemma semiprimeGaussTailPiece_eq_angularUnitWindow (H U : ℝ) {X : ℝ} (hX : 0 < X) (i j : ℕ) :
    semiprimeGaussTailPiece ℓ H U X i j =
      semiprimeGaussAngularUnitWindow ℓ (semiprimePartitionScale i/X^(2/5:ℝ))
        (semiprimePartitionScale j/X^(2/5:ℝ))
        (semiprimePartitionScale i) (semiprimePartitionScale j) H U X := by
  rw [semiprimeGaussTailPiece_window ℓ H U hX i j]
  unfold semiprimeGaussAngularUnitWindow
  rw [fullSquarefreePrimeSupport_unit,fullSquarefreePrimeSupport_unit]
  unfold productGaussWindow
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [fullPrimeCoefficient_unit hp,fullPrimeCoefficient_unit hq]
  rfl

theorem semiprimeGaussTail_angular_hecke_window
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ 0 < K ∧
      ∀ r s A B H U X : ℝ, 0 ≤ r → 0 ≤ s → 1 ≤ A → 1 ≤ B → B₀ ≤ B →
      (2*B)^(1/2:ℝ) < B → B^(1-η/4) ≤ A → A ≤ B^2/(1+Real.log B)^G →
      (1+Real.log B)^m ≤ U → U ≤ B^(7/20:ℝ) → 0 < H → 0 < X →
      ‖semiprimeGaussAngularUnitWindow ℓ r s A B H U X‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨η,G,K,B₀,m,hη,_hηone,hK,hbound⟩ := angular_full_prime_product_smoothed_height ℓ
    hpub hHuxley hperiod hMV hC (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2) hGI hGQ
    semiprimeAngularLeftLength semiprimeAngularRightLength semiprimeAngularLeftWeight semiprimeAngularRightWeight
    (fun z => z.1.2.property) (fun z => z.2.2.property) semiprimeAngularLeftLogWeights semiprimeAngularRightLogWeights
    (fun z _ _ hx => semiprimeSmoothWeight_low z.1.1 hx)
    (fun z _ _ hx => semiprimeSmoothWeight_high z.1.1 hx)
    (fun z _ _ hx => semiprimeSmoothWeight_low z.2.1 hx)
    (fun z _ _ hx => semiprimeSmoothWeight_high z.2.1 hx)
    (fun z _ x => semiprimeSmoothWeight_norm z.1.1 x)
    (fun z _ x => semiprimeSmoothWeight_norm z.2.1 x)
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth k
  refine ⟨η,G,2*K,B₀,m,hη,by positivity,?_⟩
  intro r s A B H U X hr hs hA hB hB₀ hrough hAlow hAhigh hU hUtop hH hX
  let z : SemiprimeAngularWeightParameters := ((⟨r,hr⟩,⟨A,hA⟩),(⟨s,hs⟩,⟨B,hB⟩))
  have hb := hbound z (fun _ => A) (fun _ => B) X U hB₀
    (by simp [semiprimeAngularLeftLength,z]) (by simp [semiprimeAngularRightLength,z]) (fun _ => hA)
    (fun _ => hrough) hAlow hAhigh hX hU hUtop
  simp only [semiprimeAngularLeftLength, semiprimeAngularRightLength, z] at hb
  have hUp : 0 < U := (pow_pos (by linarith [Real.log_nonneg hB]) m).trans_le hU
  apply (productGaussWindow_bound _ _ _ _ ℓ primeProductEnvelope hH hUp X).trans
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)


end CubicFirstMoment

end

end OAI
