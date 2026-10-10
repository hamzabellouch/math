import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingConvolution
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingTorus
import Mathlib.Analysis.Normed.Operator.Bilinear

namespace OAI

/-! # The uniform expanding-torus algebra -/

namespace DefocusingNLS

lemma expandingFourierCoefficient_add (a k L : ℝ) (f g : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k L (f + g) n =
      expandingFourierCoefficient a k L f n + expandingFourierCoefficient a k L g n := by
  simp only [expandingFourierCoefficient, lp.coeFn_add, Pi.add_apply, mul_add]

lemma expandingFourierCoefficient_smul (a k L : ℝ) (c : ℂ) (f : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k L (c • f) n = c * expandingFourierCoefficient a k L f n := by
  simp only [expandingFourierCoefficient, lp.coeFn_smul, Pi.smul_apply, Algebra.smul_def]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

lemma summable_expandingProductTerms (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2)
    (n : frequencyLattice) : Summable (fun m =>
      expandingFourierCoefficient a k L f m * expandingFourierCoefficient a k L g (n - m)) := by
  apply Summable.of_norm
  simpa only [norm_mul] using summable_norm_expandingProductTerms a k L ha ha1 hk hL f g n

theorem expandingProduct_comm (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2) :
    expandingProduct a k L ha ha1 hk hL f g = expandingProduct a k L ha ha1 hk hL g f := by
  ext n
  change (expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L f g n =
    (expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L g f n
  congr 1
  unfold expandingProductCoefficient
  rw [← (Equiv.subLeft n).tsum_eq (fun m =>
    expandingFourierCoefficient a k L f m * expandingFourierCoefficient a k L g (n - m))]
  simp only [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]

theorem expandingProduct_add_left (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g h : FourierL2) :
    expandingProduct a k L ha ha1 hk hL (f + g) h = expandingProduct a k L ha ha1 hk hL f h + expandingProduct a k L ha ha1 hk hL g h := by
  ext n
  change (expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L (f + g) h n =
    (expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L f h n +
      (expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L g h n
  unfold expandingProductCoefficient
  simp only [expandingFourierCoefficient_add, add_mul]
  rw [(summable_expandingProductTerms a k L ha ha1 hk hL f h n).tsum_add
    (summable_expandingProductTerms a k L ha ha1 hk hL g h n)]
  ring

theorem expandingProduct_smul_left (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (c : ℂ) (f g : FourierL2) :
    expandingProduct a k L ha ha1 hk hL (c • f) g = c • expandingProduct a k L ha ha1 hk hL f g := by
  ext n
  change (expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L (c • f) g n =
    c * ((expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L f g n)
  unfold expandingProductCoefficient
  simp only [expandingFourierCoefficient_smul, mul_assoc, tsum_mul_left]
  ring

theorem expandingProduct_add_right (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g h : FourierL2) :
    expandingProduct a k L ha ha1 hk hL f (g + h) = expandingProduct a k L ha ha1 hk hL f g + expandingProduct a k L ha ha1 hk hL f h := by
  rw [expandingProduct_comm a k L ha ha1 hk hL f (g + h), expandingProduct_add_left,
    expandingProduct_comm a k L ha ha1 hk hL g f, expandingProduct_comm a k L ha ha1 hk hL h f]

theorem expandingProduct_smul_right (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (c : ℂ) (f g : FourierL2) :
    expandingProduct a k L ha ha1 hk hL f (c • g) = c • expandingProduct a k L ha ha1 hk hL f g := by
  rw [expandingProduct_comm a k L ha ha1 hk hL f (c • g), expandingProduct_smul_left, expandingProduct_comm a k L ha ha1 hk hL g f]

/-- The exact `Y_L` product is continuous bilinear, with norm bounded independently of `L`. -/
noncomputable def expandingBilinearProduct (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    FourierL2 →L[ℂ] FourierL2 →L[ℂ] FourierL2 :=
  (LinearMap.mk₂ ℂ (expandingProduct a k L ha ha1 hk hL)
    (expandingProduct_add_left a k L ha ha1 hk hL) (expandingProduct_smul_left a k L ha ha1 hk hL)
    (expandingProduct_add_right a k L ha ha1 hk hL) (expandingProduct_smul_right a k L ha ha1 hk hL)).mkContinuous₂
      (2 * Real.sqrt (4 ^ k) * expandingEmbeddingBound a k) (expandingProduct_norm_le a k L ha ha1 hk hL)

@[simp] theorem expandingBilinearProduct_apply (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2) :
    expandingBilinearProduct a k L ha ha1 hk hL f g = expandingProduct a k L ha ha1 hk hL f g := rfl

/-- The uniform algebra product agrees with the product of represented functions. -/
theorem expandingTorusFunction_product (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2) :
    expandingTorusFunction a k L (expandingProduct a k L ha ha1 hk hL f g) =
      expandingTorusFunction a k L f * expandingTorusFunction a k L g := by
  ext x
  simp only [ContinuousMap.mul_apply, expandingTorusFunction_apply a k L ha ha1 hk hL,
    expandingProduct_coefficient]
  exact (tsum_fourier_product (expandingFourierCoefficient a k L f)
    (expandingFourierCoefficient a k L g)
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f)
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL g) x).symm

end DefocusingNLS

end OAI
