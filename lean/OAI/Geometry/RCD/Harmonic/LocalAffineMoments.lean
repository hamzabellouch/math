import OAI.Geometry.RCD.Harmonic.AffineCompactness
import OAI.Geometry.RCD.Harmonic.AffineProjection

namespace OAI

/-! # Normalized local L² moments of the actual Sobolev affine family -/

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Scaling by the norm of the constant function is the normalized local
L² convention; the zero-measure case uses the usual inverse-zero convention. -/
def normalizeLocalL2 (s : Set X) (hfin : μ s ≠ ∞)
    (f : Lp ℝ 2 (μ.restrict s)) : Lp ℝ 2 (μ.restrict s) :=
  ‖restrictedOne μ s hfin‖⁻¹ • f

omit [MetricSpace X] in
theorem restrictedOne_norm (s : Set X) (hfin : μ s ≠ ∞) :
    ‖restrictedOne μ s hfin‖ = Real.sqrt (μ.real s) := by
  unfold restrictedOne
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, Measure.real, Measure.restrict_apply_univ,
    ENNReal.toReal_ofNat, one_div]
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- Target, constant and coordinates with the same normalized local L² scale. -/
def localAffineMomentFamily {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (w : SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞) :
    Option (Option (Fin n)) → Lp ℝ 2 (μ.restrict s) :=
  affineMomentFamily n
    (normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w))
    (normalizeLocalL2 μ s hfin (restrictedOne μ s hfin))
    (fun i => normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (u i)))

/-- The finite moment expression is exactly the normalized error of the
actual Sobolev affine candidate, including its constant term. -/
theorem localAffineMomentFamily_sum {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (w : SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞)
    (c : ℝ) (v : Euclidean n) :
    (∑ i, affineErrorCoefficients c (fun j => v j) i •
      localAffineMomentFamily μ hQ u w s hfin i) =
      normalizeLocalL2 μ s hfin
        (SobolevSpace.restrictLp μ hQ s w - affineCoordinateMap μ hQ u s hfin (c, v)) := by
  rw [localAffineMomentFamily, affineMomentFamily_sum, affineCoordinateMap_apply,
    sobolevColumnMap_apply, map_sum]
  simp only [normalizeLocalL2, map_smul, smul_sub, Finset.smul_sum,
    smul_comm c (‖restrictedOne μ s hfin‖⁻¹),
    smul_comm _ (‖restrictedOne μ s hfin‖⁻¹), sub_add_eq_sub_sub]

/-- The least-squares projection has no greater normalized error than any
of the affine candidates whose joint moments are controlled. -/
theorem normalized_affineResidual_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (w : SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞) (c : ℝ) (v : Euclidean n) :
    ‖normalizeLocalL2 μ s hfin
      (affineResidual μ hQ u s hfin (SobolevSpace.restrictLp μ hQ s w))‖ ≤
        ‖∑ i, affineErrorCoefficients c (fun j => v j) i •
          localAffineMomentFamily μ hQ u w s hfin i‖ := by
  rw [localAffineMomentFamily_sum]
  simp only [normalizeLocalL2, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
  exact affineProjection_best μ hQ u s hfin (SobolevSpace.restrictLp μ hQ s w) c v

/-- Passing the finite moments to a model controls the actual normalized
least-squares residual, not just a separately chosen trial function. -/
theorem eventually_normalized_affineResidual_lt {n : ℕ}
    (u : ℕ → Fin n → SobolevSpace μ hQ) (w : ℕ → SobolevSpace μ hQ)
    (s : ℕ → Set X) (hfin : ∀ k, μ (s k) ≠ ∞)
    {Hlim : Type*} [NormedAddCommGroup Hlim] [InnerProductSpace ℝ Hlim]
    (model : Option (Option (Fin n)) → Hlim)
    (hconv : ∀ i j, Tendsto
      (fun k => ⟪localAffineMomentFamily μ hQ (u k) (w k) (s k) (hfin k) i,
        localAffineMomentFamily μ hQ (u k) (w k) (s k) (hfin k) j⟫_ℝ) atTop
      (𝓝 ⟪model i, model j⟫_ℝ))
    (c : ℝ) (v : Euclidean n) {η : ℝ}
    (hmodel : ‖∑ i, affineErrorCoefficients c (fun j => v j) i • model i‖ < η) :
    ∀ᶠ k in atTop,
      ‖normalizeLocalL2 μ (s k) (hfin k)
        (affineResidual μ hQ (u k) (s k) (hfin k)
          (SobolevSpace.restrictLp μ hQ (s k) (w k)))‖ < η := by
  have he := eventually_norm_sum_smul_lt
    (fun k => localAffineMomentFamily μ hQ (u k) (w k) (s k) (hfin k))
    model hconv (affineErrorCoefficients c (fun j => v j)) hmodel
  filter_upwards [he] with k hk
  exact lt_of_le_of_lt (normalized_affineResidual_le μ hQ (u k) (w k) (s k) (hfin k) c v) hk

end RegularPointCoordinates

end

end OAI
