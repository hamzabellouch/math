import OAI.NumberTheory.CubicMoment.Angular.AngularSmoothShortFamily
import OAI.NumberTheory.CubicMoment.Estimates.ShortProductSize

namespace OAI

/-! Uniform size bound for angular short products, used for Mellin tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem angular_smooth_short_product_size (ℓ : ℤ) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ)
      (t : ι → ℝ) (a b : Eisenstein),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∏ i, X i) ≤ D*Y → primary a → primary b →
      ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) a b (q i) (η i) (W i) (X i/2) (t i)‖ ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := short_family_product_size (ι := ι)
  refine ⟨C*D^2,mul_pos hC (sq_pos_of_pos hD),?_⟩
  intro F Y X A q η W t a b hA hX hq hW hcut hprod ha hb
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 a b ha hb
  simp only [K,angularShortFamily_mixedValue ℓ F X A q η W t hA hX hq hW hcut] at h
  apply h.trans
  have hp := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hX i))) hprod 2
  calc
    _ ≤ C*(D*Y)^2 := mul_le_mul_of_nonneg_left hp hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
