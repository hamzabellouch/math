import OAI.Geometry.RCD.Harmonic.RadialDerivativeError
import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # The averaged size of the actual radial pairing -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Pointwise gradient bounds give the normalized L² size used to show
that the center values of affine fits vanish at shrinking radii. -/
theorem normalized_gamma_size (s : Set X) (hs : μ s ≠ ∞) (hs0 : μ s ≠ 0)
    (q a : SobolevSpace μ hQ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ q q x ≤ A)
    (ha : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ a a x ≤ B) :
    ‖normalizeLocalL2 μ s hs
      ((localGamma_memLp_two_of_bound μ hQ s q a ha).toLp (localGamma μ hQ q a))‖ ≤
        Real.sqrt (A * B) := by
  let rawmem := localGamma_memLp_two_of_bound μ hQ s q a ha
  let raw := rawmem.toLp (localGamma μ hQ q a)
  have hpoint : ∀ᵐ x ∂μ.restrict s, (raw x) ^ 2 ≤ A * B := by
    filter_upwards [MemLp.coeFn_toLp rawmem, hq, ha,
      ae_restrict_of_ae (localGamma_sq_le μ hQ q a),
      ae_restrict_of_ae (localGamma_self μ hQ a)] with x he hqx hax hcs hself
    change raw x = localGamma μ hQ q a x at he
    rw [he]
    exact hcs.trans (mul_le_mul hqx hax (by rw [hself]; positivity) hA)
  let : IsFiniteMeasure (μ.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hs.lt_top⟩
  have hi : (∫ x, (raw x) ^ 2 ∂μ.restrict s) ≤ (A * B) * μ.real s := by
    calc
      _ ≤ ∫ _x, A * B ∂μ.restrict s :=
        integral_mono_ae (Lp.memLp raw).integrable_sq (integrable_const _) hpoint
      _ = _ := by simp only [integral_const, smul_eq_mul, Measure.real,
        Measure.restrict_apply_univ, mul_comm]
  have hvol : μ.real s ≠ 0 := ne_of_gt (ENNReal.toReal_pos hs0 hs)
  have hn : ‖normalizeLocalL2 μ s hs raw‖ ^ 2 ≤ A * B := by
    rw [normalizeLocalL2_norm_sq]
    have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (μ.real s)⁻¹)
    exact hm.trans_eq (by field_simp [hvol])
  change ‖normalizeLocalL2 μ s hs raw‖ ≤ _
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (by simpa only [Real.sq_sqrt (mul_nonneg hA hB)] using hn)

end RegularPointCoordinates

end

end OAI
