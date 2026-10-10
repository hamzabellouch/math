import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.VectorL2PairingBounds

namespace OAI

/-!
# Transferring scalar Bessel bounds to vector fields

Scalar-vector pairings commute with the Bochner integral, and the squared native
`L²` norm agrees with the integral of the squared pointwise norm. Expanding in an
orthonormal basis transfers a finite scalar Bessel bound to pairings of a vector
field against test vectors of norm at most one, with the same Bessel constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

theorem memLp_inner_const_of_vector {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (u : X → E) (hu : MemLp u 2 μ) (e : E) :
    MemLp (fun x => inner ℝ e (u x)) 2 μ :=
  hu.of_le_mul (aestronglyMeasurable_const.inner hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => norm_inner_le_norm (𝕜 := ℝ) e (u x))

theorem integral_scalar_vector_pairing {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (f : X → ℝ) (u : X → E)
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (e : E) :
    (∫ x, f x * inner ℝ e (u x) ∂μ) = inner ℝ e (∫ x, f x • u x ∂μ) := by
  have hi : Integrable (fun x => f x • u x) μ := memLp_one_iff_integrable.mp (hf.smul hu)
  simpa only [real_inner_smul_right] using! (integral_inner (𝕜 := ℝ) hi e)

theorem toLp_vector_norm_sq_eq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (u : X → E) (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem vector_sq_integral_of_native_norm_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (f : X → ℝ) (u : X → E)
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (D : ℝ≥0)
    (hN : eLpNorm u 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    (∫ x, ‖u x‖ ^ 2 ∂μ) ≤ (D : ℝ) ^ 2 * ∫ x, f x ^ 2 ∂μ := by
  have hfin : (D : ℝ≥0∞) * eLpNorm f 2 μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hf.eLpNorm_ne_top
  have hnorm : ‖hu.toLp u‖ ≤ (D : ℝ) * ‖hf.toLp f‖ := by
    simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.coe_toReal] using!
      ENNReal.toReal_mono hfin hN
  rw [← toLp_vector_norm_sq_eq_integral μ u hu, ← toLp_norm_sq_eq_integral μ f hf]
  have hh := mul_self_le_mul_self (norm_nonneg (hu.toLp u)) hnorm
  nlinarith

theorem finite_vector_bessel_of_scalar {ι κ X E : Type*} [Fintype κ]
    [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : OrthonormalBasis κ ℝ E) (μ : Measure X) (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (B : ℝ)
    (hb : ∀ v : X → ℝ, MemLp v 2 μ →
      ∑ i ∈ s, (∫ x, f i x * v x ∂μ) ^ 2 ≤ B * ∫ x, v x ^ 2 ∂μ)
    (u : X → E) (hu : MemLp u 2 μ) (e : ι → E)
    (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, f i x * inner ℝ (e i) (u x) ∂μ) ^ 2 ≤
      B * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  classical
  let v : ι → E := fun i => ∫ x, f i x • u x ∂μ
  have hv (i : ι) (hi : i ∈ s) :
      (∫ x, f i x * inner ℝ (e i) (u x) ∂μ) ^ 2 ≤ ‖v i‖ ^ 2 := by
    rw [integral_scalar_vector_pairing μ (f i) u (hf i) hu (e i)]
    have hnorm : |inner ℝ (e i) (v i)| ≤ ‖v i‖ := by
      calc
        _ ≤ ‖e i‖ * ‖v i‖ := by
          simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) (e i) (v i)
        _ ≤ 1 * ‖v i‖ := mul_le_mul_of_nonneg_right (he i hi) (norm_nonneg _)
        _ = _ := one_mul _
    have hh := mul_self_le_mul_self (abs_nonneg _) hnorm
    simpa only [← pow_two, sq_abs] using! hh
  have hcoord (k : κ) := memLp_inner_const_of_vector μ u hu (b k)
  calc
    _ ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := Finset.sum_le_sum hv
    _ = ∑ k : κ, ∑ i ∈ s, (∫ x, f i x * inner ℝ (b k) (u x) ∂μ) ^ 2 := by
      dsimp only [v]
      simp_rw [← b.sum_sq_inner_right, ← integral_scalar_vector_pairing μ _ u (hf _) hu]
      exact Finset.sum_comm
    _ ≤ ∑ k : κ, B * ∫ x, (inner ℝ (b k) (u x)) ^ 2 ∂μ :=
      Finset.sum_le_sum (fun k _ => hb _ (hcoord k))
    _ = B * ∫ x, ‖u x‖ ^ 2 ∂μ := by
      rw [← Finset.mul_sum, ← integral_finsetSum _ (fun k _ => (hcoord k).integrable_sq)]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => b.sum_sq_inner_right (u x)

end

end RieszRectifiability

end OAI
