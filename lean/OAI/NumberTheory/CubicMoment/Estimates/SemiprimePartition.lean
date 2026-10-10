import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeSmoothWeights

namespace OAI

/-! The finite smooth partition of the original semiprime kernel. Every
prime coordinate retains both its roughness weight and the total-product
cutoff; the displayed number of pieces is the actual finite partition. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def semiprimePartitionScale (j : ℕ) : ℝ := (4/3:ℝ)^j/2

lemma semiprimePartitionScale_pos (j : ℕ) : 0 < semiprimePartitionScale j := by
  unfold semiprimePartitionScale
  positivity

def semiprimePartitionCoefficient (X : ℝ) (j : ℕ) (p : Eisenstein) : ℂ :=
  semiprimeSmoothWeight (semiprimePartitionScale j/(X^(2/5:ℝ)))
    (norm p/semiprimePartitionScale j)

lemma semiprimePartitionCoefficient_sum {X : ℝ} (hX : 1 ≤ X)
    {p : Eisenstein} (hp : p ∈ primeCutoff (3*X)) :
    (∑ j ∈ Finset.range (normPartitionCount (3*X)), semiprimePartitionCoefficient X j p) =
      semiprimeRoughWeight X p := by
  have h := normPartitionWeight_partition
    (one_le_norm (mem_primeCutoff.mp hp).1.2.ne_zero) (mem_primeCutoff.mp hp).2
    (normPartitionCount_covers (by linarith : (1:ℝ) ≤ 3*X))
  calc
    _ = ∑ j ∈ Finset.range (normPartitionCount (3*X)), semiprimeRoughWeight X p*
        normPartitionWeight (2*norm p/(4/3:ℝ)^j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [semiprimePartitionCoefficient,semiprimeSmoothWeight_at_prime X
        (semiprimePartitionScale_pos j),normPartitionWeight_scale]
      rfl
    _ = _ := by rw [← Finset.mul_sum,h,mul_one]

def semiprimePartitionPiece (ℓ : ℤ) (H T X : ℝ) (i j : ℕ) : ℂ :=
  ∑ p ∈ primeCutoff (3*X), ∑ q ∈ primeCutoff (3*X),
    semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
      centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q)

theorem centralSemiprimeProduct_partition (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 1 ≤ X) :
    centralSemiprimeProduct ℓ H T X = (1/2:ℂ)*
      ∑ i ∈ Finset.range (normPartitionCount (3*X)),
        ∑ j ∈ Finset.range (normPartitionCount (3*X)), semiprimePartitionPiece ℓ H T X i j := by
  rw [centralSemiprimeProduct_eq_bilinear ℓ H T (zero_lt_one.trans_le hX)]
  congr 1
  calc
    _ = ∑ p ∈ primeCutoff (3*X), ∑ q ∈ primeCutoff (3*X),
        ∑ i ∈ Finset.range (normPartitionCount (3*X)),
          ∑ j ∈ Finset.range (normPartitionCount (3*X)),
            semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
              centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q) := by
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

end CubicFirstMoment

end

end OAI
