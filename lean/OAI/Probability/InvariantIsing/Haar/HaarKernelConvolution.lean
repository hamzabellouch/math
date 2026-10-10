import OAI.Probability.InvariantIsing.Haar.HaarFrobeniusGeometry
import OAI.Probability.InvariantIsing.Haar.HaarGroupTopology

namespace OAI

/-! Haar convolution by a positive polynomial kernel preserves Lipschitz constants. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set
open scoped BigOperators
namespace InvariantIsing

lemma continuous_haarKernelBase {N : ℕ} (U : SpecialOrthogonal N) :
    Continuous (haarKernelBase U) := by
  unfold haarKernelBase
  apply continuous_const.add
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_apply j).comp
    ((continuous_apply i).comp continuous_subtype_val))

def haarKernelMass {N : ℕ} (μ : Measure (SpecialOrthogonal N)) (n : ℕ) : ℝ :=
  ∫ V, (haarKernelBase 1 V)^n ∂μ

def haarKernelApprox {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (f : SpecialOrthogonal N → ℝ) (n : ℕ) : MatrixPolynomial N :=
  (haarKernelMass μ n)⁻¹ • haarKernelAverage μ f n

lemma haarKernelMass_pos {N : ℕ} (hN : 0 < N) (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (n : ℕ) :
    0 < haarKernelMass μ n := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := (1 : SpecialOrthogonal N))
    ((continuous_haarKernelBase 1).pow n)
    (continuous_haar_integrable μ _ ((continuous_haarKernelBase 1).pow n))
    (fun V => pow_nonneg (haarKernelBase_nonneg 1 V) n)
  change (haarKernelBase 1 1)^n ≠ 0
  rw [haarKernelBase_self]
  exact (pow_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hN)) n).ne'

lemma haarKernelAverage_convolution {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (f : SpecialOrthogonal N → ℝ)
    (hf : Continuous f) (n : ℕ) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarKernelAverage μ f n) U =
      ∫ V, f (U*V)*(haarKernelBase 1 V)^n ∂μ := by
  rw [haarKernelAverage_value μ f hf]
  have h := integral_mul_left_eq_self (μ := μ)
    (fun V => f V*(haarKernelBase U V)^n) U
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all μ fun V => by
    dsimp only
    rw [show haarKernelBase U (U*V) = haarKernelBase 1 V by
      simpa only [mul_one] using haarKernelBase_mul_left U 1 V]

theorem haarKernelApprox_lipschitz {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ)
    (hL : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) (n : ℕ)
    (U V : SpecialOrthogonal N) :
    |haarPolynomialValue (haarKernelApprox μ f n) U-
      haarPolynomialValue (haarKernelApprox μ f n) V| ≤ L*frobeniusDistance U V := by
  have hZ := haarKernelMass_pos hN μ n
  let k (W : SpecialOrthogonal N) := (haarKernelBase 1 W)^n
  have hk : Continuous k := (continuous_haarKernelBase 1).pow n
  have hi (U : SpecialOrthogonal N) : Integrable (fun W => f (U*W)*k W) μ :=
    continuous_haar_integrable μ _ ((hf.comp (continuous_const.mul continuous_id)).mul hk)
  have he (U : SpecialOrthogonal N) : haarPolynomialValue (haarKernelApprox μ f n) U =
      (haarKernelMass μ n)⁻¹*(∫ W, f (U*W)*k W ∂μ) := by
    simp only [haarKernelApprox,haarPolynomialValue,map_smul,smul_eq_mul]
    change (haarKernelMass μ n)⁻¹*haarPolynomialValue (haarKernelAverage μ f n) U = _
    rw [haarKernelAverage_convolution μ f hf]
  rw [he U,he V,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hZ),← integral_sub (hi U) (hi V)]
  apply (inv_mul_le_iff₀ hZ).mpr
  calc
    |∫ W, (f (U*W)*k W-f (V*W)*k W) ∂μ| ≤
        ∫ W, |f (U*W)*k W-f (V*W)*k W| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ W, (L*frobeniusDistance U V)*k W ∂μ := by
      apply integral_mono
      · exact ((hi U).sub (hi V)).abs
      · exact (continuous_haar_integrable μ _ hk).const_mul _
      · intro W
        dsimp only
        rw [← sub_mul,abs_mul,abs_of_nonneg (pow_nonneg (haarKernelBase_nonneg 1 W) n)]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (haarKernelBase_nonneg 1 W) n)
        exact (hL (U*W) (V*W)).trans_eq (by rw [frobeniusDistance_mul_right])
    _ = haarKernelMass μ n*(L*frobeniusDistance U V) := by
      rw [integral_const_mul,mul_comm]
      rfl

end InvariantIsing

end

end OAI
