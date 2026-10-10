import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailIdentity
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeFullSupport
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailWindow

namespace OAI

/-! Exact smooth coordinate partition of each literal semiprime Gauss window.
The finite prime cutoff and the original product envelope are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def semiprimeGaussTailPiece (ℓ : ℤ) (H T X : ℝ) (i j : ℕ) : ℂ :=
  ∑ p ∈ primeCutoff (3*X), ∑ q ∈ primeCutoff (3*X),
    semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
      scaleFirstTailKernel ℓ H T X (p*q)

theorem scaleFirstTailSemiprimeWindow_partition (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 1 ≤ X) :
    scaleFirstTailSemiprimeWindow ℓ H T X = (1/2:ℂ)*
      ∑ i ∈ Finset.range (normPartitionCount (3*X)),
        ∑ j ∈ Finset.range (normPartitionCount (3*X)), semiprimeGaussTailPiece ℓ H T X i j := by
  rw [scaleFirstTailSemiprimeWindow_eq_bilinear ℓ H T (zero_lt_one.trans_le hX)]
  congr 1
  calc
    _ = ∑ p ∈ primeCutoff (3*X), ∑ q ∈ primeCutoff (3*X),
        ∑ i ∈ Finset.range (normPartitionCount (3*X)),
          ∑ j ∈ Finset.range (normPartitionCount (3*X)),
            semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
              scaleFirstTailKernel ℓ H T X (p*q) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [← semiprimePartitionCoefficient_sum hX hp,← semiprimePartitionCoefficient_sum hX hq]
      simp_rw [Finset.sum_mul,Finset.mul_sum,Finset.sum_mul]
    _ = _ := by
      simp_rw [Finset.sum_comm (s := primeCutoff (3*X))
        (t := Finset.range (normPartitionCount (3*X)))]
      rfl

lemma scaleFirstTailKernel_large_factor (ℓ : ℤ) (H T : ℝ) {X : ℝ} (hX : 0 < X)
    {p q : Eisenstein} (hp : primary p) (hq : primary q)
    (hlarge : 3*X < norm p ∨ 3*X < norm q) :
    scaleFirstTailKernel ℓ H T X (p*q) = 0 := by
  have hn : 3*X < norm (p*q) := by
    rw [norm_mul_eq]
    rcases hlarge with hlarge | hlarge
    · exact hlarge.trans_le (le_mul_of_one_le_right (norm_nonneg p)
        (one_le_norm (primary_ne_zero hq)))
    · exact hlarge.trans_le (le_mul_of_one_le_left (norm_nonneg q)
        (one_le_norm (primary_ne_zero hp)))
  have hz := primeProductEnvelope_zero ((le_div_iff₀ hX).mpr hn.le)
  simp only [scaleFirstTailKernel,hz,mul_zero,zero_mul]

theorem semiprimeGaussTailPiece_full_support (ℓ : ℤ) (H T : ℝ) {X : ℝ} (hX : 0 < X)
    (i j : ℕ) :
    semiprimeGaussTailPiece ℓ H T X i j =
      ∑ p ∈ semiprimeFullSupport X i, ∑ q ∈ semiprimeFullSupport X j,
        semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
          scaleFirstTailKernel ℓ H T X (p*q) := by
  let F : Eisenstein × Eisenstein → ℂ := fun z =>
    semiprimePartitionCoefficient X i z.1*semiprimePartitionCoefficient X j z.2*
      scaleFirstTailKernel ℓ H T X (z.1*z.2)
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
      have hzero := scaleFirstTailKernel_large_factor ℓ H T hX hp.1 hq.1 hlarge
      simp only [F,hzero,mul_zero]
    · intro z _ _
      rfl
  simpa only [Finset.product_eq_sprod,Finset.sum_product,F,semiprimeGaussTailPiece] using he


lemma semiprimeGaussTailPiece_window (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X)
    (i j : ℕ) : semiprimeGaussTailPiece ℓ H U X i j =
      productGaussWindow (semiprimeFullSupport X i) (semiprimeFullSupport X j)
        (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j)
        ℓ primeProductEnvelope H U X := by
  rw [semiprimeGaussTailPiece_full_support ℓ H U hX i j]
  rfl

end CubicFirstMoment

end

end OAI
