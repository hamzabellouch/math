import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailWindows
import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailProductEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeHeight

namespace OAI

/-! Both analytic height ranges on the original smooth rough-prime weights.
The parameter families retain their actual transition ratios. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

private abbrev SemiprimeTailParameters := (Ici (0:ℝ) × Ici (1:ℝ)) × (Ici (0:ℝ) × Ici (1:ℝ))
private def semiTailLeft (z : SemiprimeTailParameters) : ℝ := z.1.2
private def semiTailRight (z : SemiprimeTailParameters) : ℝ := z.2.2
private def semiTailLeftWeight (z : SemiprimeTailParameters) (_ : Unit) : ℝ → ℂ :=
  semiprimeSmoothWeight z.1.1
private def semiTailRightWeight (z : SemiprimeTailParameters) (_ : Unit) : ℝ → ℂ :=
  semiprimeSmoothWeight z.2.1

private def semiTailLeftFamily :
    LogarithmicWeightFamily (fun z : SemiprimeTailParameters × Unit => semiTailLeft z.1)
      (fun z => semiTailLeftWeight z.1 z.2) :=
  uniformLogWeights_prime_coordinates semiTailLeft
    (fun z => semiprimeSmoothWeight z.1.1) (fun z => z.1.2.property)
    (semiprimeSmoothWeights.reindex (fun z : SemiprimeTailParameters => z.1.1))

private def semiTailRightFamily :
    LogarithmicWeightFamily (fun z : SemiprimeTailParameters × Unit => semiTailRight z.1)
      (fun z => semiTailRightWeight z.1 z.2) :=
  uniformLogWeights_prime_coordinates semiTailRight
    (fun z => semiprimeSmoothWeight z.2.1) (fun z => z.2.2.property)
    (semiprimeSmoothWeights.reindex (fun z : SemiprimeTailParameters => z.2.1))

def semiprimeGaussUnitWindow (r s A B H U X : ℝ) : ℂ :=
  productGaussWindow
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) 1)
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A))
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B))
    0 primeProductEnvelope H U X

def semiprimeGaussUnitTail (r s A B H U X : ℝ) : ℂ :=
  envelopeCutoffBilinearTail
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) 1)
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A))
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B))
    primeProductEnvelope H U X

lemma semiprimeGaussTailPiece_eq_unitWindow (H U : ℝ) {X : ℝ} (hX : 0 < X) (i j : ℕ) :
    semiprimeGaussTailPiece 0 H U X i j =
      semiprimeGaussUnitWindow (semiprimePartitionScale i/X^(2/5:ℝ))
        (semiprimePartitionScale j/X^(2/5:ℝ))
        (semiprimePartitionScale i) (semiprimePartitionScale j) H U X := by
  rw [semiprimeGaussTailPiece_window 0 H U hX i j]
  unfold semiprimeGaussUnitWindow
  rw [fullSquarefreePrimeSupport_unit,fullSquarefreePrimeSupport_unit]
  unfold productGaussWindow
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [fullPrimeCoefficient_unit hp,fullPrimeCoefficient_unit hq]
  rfl

theorem semiprimeGaussTail_hecke_window
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ 0 < K ∧
      ∀ r s A B H U X : ℝ, 0 ≤ r → 0 ≤ s → 1 ≤ A → 1 ≤ B → B₀ ≤ B →
      (2*B)^(1/2:ℝ) < B → B^(1-η/4) ≤ A → A ≤ B^2/(1+Real.log B)^G →
      (1+Real.log B)^m ≤ U → U ≤ B^(7/20:ℝ) → 0 < H → 0 < X →
      ‖semiprimeGaussUnitWindow r s A B H U X‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨η,G,K,B₀,m,hη,_hηone,hK,hbound⟩ := full_prime_product_smoothed_height
    hpub hHuxley hperiod hMV hC (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2) hGI hGQ
    semiTailLeft semiTailRight semiTailLeftWeight semiTailRightWeight
    (fun z => z.1.2.property) (fun z => z.2.2.property) semiTailLeftFamily semiTailRightFamily
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
  let z : SemiprimeTailParameters := ((⟨r,hr⟩,⟨A,hA⟩),(⟨s,hs⟩,⟨B,hB⟩))
  have hb := hbound z (fun _ => A) (fun _ => B) X U hB₀
    (by simp [semiTailLeft,z]) (by simp [semiTailRight,z]) (fun _ => hA)
    (fun _ => hrough) hAlow hAhigh hX hU hUtop
  simp only [semiTailLeft, semiTailRight, z] at hb
  have hUp : 0 < U := (pow_pos (by linarith [Real.log_nonneg hB]) m).trans_le hU
  apply (productGaussWindow_bound _ _ _ _ 0 primeProductEnvelope hH hUp X).trans
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)

theorem semiprimeGaussTail_middle_tail
    (hHuxley : HuxleyAdditiveLargeSieve) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ r s A B H U X : ℝ,
      0 ≤ r → 0 ≤ s → 1 ≤ A → 1 ≤ B → B₀ ≤ B →
      (4*B)^(27/25:ℝ) ≤ A → A ≤ B^(19/10:ℝ) →
      (4*B)^(1/50:ℝ) ≤ U → 1 ≤ H → H ≤ B^3 → 0 < X →
      ‖semiprimeGaussUnitTail r s A B H U X‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨K,B₀,hK,hbound⟩ := primeGroupTail_full_prime_envelope_tail
    hHuxley hMV hC (by norm_num : (1:ℝ) ≤ 2)
    semiTailLeft semiTailRight semiTailLeftWeight semiTailRightWeight
    (fun z => z.1.2.property) (fun z => z.2.2.property) semiTailLeftFamily semiTailRightFamily
    (fun z _ _ hx => semiprimeSmoothWeight_low z.1.1 hx)
    (fun z _ _ hx => semiprimeSmoothWeight_high z.1.1 hx)
    (fun z _ _ hx => semiprimeSmoothWeight_low z.2.1 hx)
    (fun z _ _ hx => semiprimeSmoothWeight_high z.2.1 hx) k
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth
  refine ⟨K,B₀,hK,?_⟩
  intro r s A B H U X hr hs hA hB hB₀ hAlow hAhigh hU hH hHB hX
  let z : SemiprimeTailParameters := ((⟨r,hr⟩,⟨A,hA⟩),(⟨s,hs⟩,⟨B,hB⟩))
  exact hbound z (fun _ => A) (fun _ => B) 1 1 H U X hB₀
    (by simp [semiTailLeft,z]) (by simp [semiTailRight,z]) (fun _ => hA)
    (fun _ => hB) (by simpa [semiTailLeft, semiTailRight, z,
      show (2:ℝ)*2=4 by norm_num] using hAlow)
    hAhigh (by simpa [semiTailRight, z, show (2:ℝ)*2=4 by norm_num] using hU) hH hHB hX

theorem semiprimeGaussTail_middle_window
    (hHuxley : HuxleyAdditiveLargeSieve) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ r s A B H U X : ℝ,
      0 ≤ r → 0 ≤ s → 1 ≤ A → 1 ≤ B → B₀ ≤ B →
      (4*B)^(27/25:ℝ) ≤ A → A ≤ B^(19/10:ℝ) →
      (4*B)^(1/50:ℝ) ≤ U → 1 ≤ H → H ≤ B^3 → 0 < X →
      U < 2*Real.pi*H →
      ‖semiprimeGaussUnitWindow r s A B H U X‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨K,B₀,hK,hbound⟩ := semiprimeGaussTail_middle_tail hHuxley hMV hC k
  refine ⟨2*K,B₀,by positivity,?_⟩
  intro r s A B H U X hr hs hA hB hB₀ hAlow hAhigh hU hH hHB hX hcap
  have hUp : 0 < U := (Real.rpow_pos_of_pos (by positivity : 0 < 4*B) _).trans_le hU
  have hU' : (4*B)^(1/50:ℝ) ≤ U*(3/2) := hU.trans (by linarith)
  have hfirst := hbound r s A B H U X hr hs hA hB hB₀ hAlow hAhigh hU hH hHB hX
  have hlast := hbound r s A B H (U*(3/2)) X hr hs hA hB hB₀ hAlow hAhigh hU' hH hHB hX
  have he : semiprimeGaussUnitWindow r s A B H U X =
      semiprimeGaussUnitTail r s A B H U X-
        semiprimeGaussUnitTail r s A B H (U*(3/2)) X :=
    productGaussWindow_eq_tail_sub _ _ _ _ _ (zero_lt_one.trans_le hH) hUp hcap X
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hfirst hlast).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
