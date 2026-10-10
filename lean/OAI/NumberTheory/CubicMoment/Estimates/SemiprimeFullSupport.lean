import OAI.NumberTheory.CubicMoment.Estimates.SemiprimePartition
import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeSupport

namespace OAI

/-! In a semiprime piece the full independent smooth prime supports can
replace the auxiliary cutoff at 3X. Extra primes give a zero product
envelope; missing primes have zero coordinate weight. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def semiprimeFullSupport (X : ℝ) (i : ℕ) : Finset Eisenstein :=
  fullPrimeSupport 2
    (fun _ : Unit => semiprimeSmoothWeight (semiprimePartitionScale i/(X^(2/5:ℝ))))
    (fun _ => semiprimePartitionScale i) ()

lemma semiprimeFullSupport_mem (X : ℝ) (i : ℕ) (p : Eisenstein) :
    p ∈ semiprimeFullSupport X i ↔
      primaryPrime p ∧ semiprimePartitionCoefficient X i p ≠ 0 :=
  fullPrimeSupport_mem_iff _ _ (fun _ => semiprimePartitionScale_pos i)
    (fun _ _ hx => semiprimeSmoothWeight_high _ hx) () p

lemma centeredHeightKernel_large_factor (ℓ : ℤ) (H T : ℝ) {X : ℝ} (hX : 0 < X)
    {p q : Eisenstein} (hp : primary p) (hq : primary q)
    (hlarge : 3*X < norm p ∨ 3*X < norm q) :
    centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q) = 0 := by
  have hn : 3*X < norm (p*q) := by
    rw [norm_mul_eq]
    rcases hlarge with hlarge | hlarge
    · exact hlarge.trans_le (le_mul_of_one_le_right (norm_nonneg p)
        (one_le_norm (primary_ne_zero hq)))
    · exact hlarge.trans_le (le_mul_of_one_le_left (norm_nonneg q)
        (one_le_norm (primary_ne_zero hp)))
  have hz := primeProductEnvelope_zero ((le_div_iff₀ hX).mpr hn.le)
  simp only [centeredHeightKernel,hz,mul_zero,zero_mul]

theorem semiprimePartitionPiece_full_support (ℓ : ℤ) (H T : ℝ) {X : ℝ} (hX : 0 < X)
    (i j : ℕ) :
    semiprimePartitionPiece ℓ H T X i j =
      ∑ p ∈ semiprimeFullSupport X i, ∑ q ∈ semiprimeFullSupport X j,
        semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
          centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q) := by
  let F : Eisenstein × Eisenstein → ℂ := fun z =>
    semiprimePartitionCoefficient X i z.1*semiprimePartitionCoefficient X j z.2*
      centeredHeightKernel ℓ primeProductEnvelope H T X X (z.1*z.2)
  have he : (∑ z ∈ (primeCutoff (3*X)).product (primeCutoff (3*X)), F z) =
      ∑ z ∈ (semiprimeFullSupport X i).product (semiprimeFullSupport X j), F z := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro z hz hout
      have hp := (mem_primeCutoff.mp (Finset.mem_product.mp hz).1).1
      have hq := (mem_primeCutoff.mp (Finset.mem_product.mp hz).2).1
      have hzero : semiprimePartitionCoefficient X i z.1 = 0 ∨
          semiprimePartitionCoefficient X j z.2 = 0 := by
        by_contra hn
        push Not at hn
        exact hout (Finset.mem_product.mpr
          ⟨(semiprimeFullSupport_mem X i z.1).mpr ⟨hp,hn.1⟩,
            (semiprimeFullSupport_mem X j z.2).mpr ⟨hq,hn.2⟩⟩)
      rcases hzero with hzero | hzero <;> simp only [F,hzero,mul_zero,zero_mul]
    · intro z hz hout
      have hp := ((semiprimeFullSupport_mem X i z.1).mp (Finset.mem_product.mp hz).1).1
      have hq := ((semiprimeFullSupport_mem X j z.2).mp (Finset.mem_product.mp hz).2).1
      have hlarge : 3*X < norm z.1 ∨ 3*X < norm z.2 := by
        by_contra hn
        push Not at hn
        exact hout (Finset.mem_product.mpr
          ⟨mem_primeCutoff.mpr ⟨hp,hn.1⟩,mem_primeCutoff.mpr ⟨hq,hn.2⟩⟩)
      have hzero := centeredHeightKernel_large_factor ℓ H T hX hp.1 hq.1 hlarge
      simp only [F,hzero,mul_zero]
    · intro z _ _
      rfl
  simpa only [Finset.product_eq_sprod,Finset.sum_product,F,semiprimePartitionPiece] using he

end CubicFirstMoment

end

end OAI
