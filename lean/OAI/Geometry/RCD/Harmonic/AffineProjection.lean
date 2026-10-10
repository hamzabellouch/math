import OAI.Geometry.RCD.Harmonic.HarmonicGrams

namespace OAI

/-! # The actual `L²` projection onto the affine coordinate span -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞)

def restrictedOne : Lp ℝ 2 (μ.restrict s) :=
  indicatorConstLp 2 MeasurableSet.univ (by simpa using hfin) 1

/-- Constants and linear combinations of the given coordinates, restricted
as actual `L²` functions on the testing set. -/
def affineCoordinateMap : (ℝ × Euclidean n) →L[ℝ] Lp ℝ 2 (μ.restrict s) :=
  (ContinuousLinearMap.fst ℝ ℝ (Euclidean n)).smulRight (restrictedOne μ s hfin) +
    (SobolevSpace.restrictLp μ hQ s).comp
      ((sobolevColumnMap μ hQ u).comp (ContinuousLinearMap.snd ℝ ℝ (Euclidean n)))

theorem affineCoordinateMap_apply (c : ℝ) (v : Euclidean n) :
    affineCoordinateMap μ hQ u s hfin (c, v) =
      c • restrictedOne μ s hfin +
      SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u v) := rfl

def affineCoordinateSpace : Submodule ℝ (Lp ℝ 2 (μ.restrict s)) :=
  (affineCoordinateMap μ hQ u s hfin).range

instance affineCoordinateSpace_finiteDimensional :
    FiniteDimensional ℝ (affineCoordinateSpace μ hQ u s hfin) :=
  LinearMap.finiteDimensional_range _

/-- The least-squares affine fit exists without assuming independence of
its generators. Coefficient uniqueness can be added after normalization. -/
def affineProjection : Lp ℝ 2 (μ.restrict s) →L[ℝ] Lp ℝ 2 (μ.restrict s) :=
  (affineCoordinateSpace μ hQ u s hfin).starProjection

theorem affineProjection_has_coefficients (f : Lp ℝ 2 (μ.restrict s)) :
    ∃ c : ℝ, ∃ v : Euclidean n,
      affineProjection μ hQ u s hfin f = c • restrictedOne μ s hfin +
        SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u v) := by
  have hm := (affineCoordinateSpace μ hQ u s hfin).starProjection_apply_mem f
  rcases hm with ⟨⟨c, v⟩, hcv⟩
  exact ⟨c, v, hcv.symm⟩

theorem affineProjection_orthogonal (f : Lp ℝ 2 (μ.restrict s))
    (c : ℝ) (v : Euclidean n) :
    ⟪f - affineProjection μ hQ u s hfin f,
      affineCoordinateMap μ hQ u s hfin (c, v)⟫_ℝ = 0 :=
  (affineCoordinateSpace μ hQ u s hfin).starProjection_inner_eq_zero f _ ⟨(c, v), rfl⟩

/-- The affine fit minimizes the `L²` error among all coordinate-affine
functions, with the unnormalized integral convention. -/
theorem affineProjection_best (f : Lp ℝ 2 (μ.restrict s))
    (c : ℝ) (v : Euclidean n) :
    ‖f - affineProjection μ hQ u s hfin f‖ ≤
      ‖f - affineCoordinateMap μ hQ u s hfin (c, v)‖ := by
  let K := affineCoordinateSpace μ hQ u s hfin
  let P := affineProjection μ hQ u s hfin
  let g := affineCoordinateMap μ hQ u s hfin (c, v)
  have hm : P f - g ∈ K := K.sub_mem (K.starProjection_apply_mem f) ⟨(c, v), rfl⟩
  have ho : ⟪f - P f, P f - g⟫_ℝ = 0 := K.starProjection_inner_eq_zero f _ hm
  have he := norm_add_sq_real (f - P f) (P f - g)
  have hs : f - P f + (P f - g) = f - g := by abel
  rw [hs, ho] at he
  change ‖f - P f‖ ≤ ‖f - g‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖P f - g‖])

/-- The residual is a bounded linear map, so all scalar directional fits
can be assembled linearly before taking their matrix coefficients. -/
def affineResidual : Lp ℝ 2 (μ.restrict s) →L[ℝ] Lp ℝ 2 (μ.restrict s) :=
  ContinuousLinearMap.id ℝ _ - affineProjection μ hQ u s hfin

theorem affineResidual_norm_le (f : Lp ℝ 2 (μ.restrict s)) :
    ‖affineResidual μ hQ u s hfin f‖ ≤ ‖f‖ := by
  have hb := affineProjection_best μ hQ u s hfin f 0 0
  change ‖f - affineProjection μ hQ u s hfin f‖ ≤
    ‖f - affineCoordinateMap μ hQ u s hfin 0‖ at hb
  simpa only [map_zero, sub_zero, affineResidual, sub_apply,
    ContinuousLinearMap.id_apply] using hb

theorem affineProjection_norm_le (f : Lp ℝ 2 (μ.restrict s)) :
    ‖affineProjection μ hQ u s hfin f‖ ≤ ‖f‖ :=
  (affineCoordinateSpace μ hQ u s hfin).norm_starProjection_apply_le f

/-- Orthogonality to constants is the vanishing of the actual integral,
including when the original ambient measure is infinite. -/
theorem affineResidual_integral (f : Lp ℝ 2 (μ.restrict s)) :
    ∫ x, affineResidual μ hQ u s hfin f x ∂μ.restrict s = 0 := by
  have ho := affineProjection_orthogonal μ hQ u s hfin f 1 0
  have hi := L2.inner_indicatorConstLp_one
    (μ := μ.restrict s) MeasurableSet.univ (by simpa using hfin)
    (affineResidual μ hQ u s hfin f)
  have ho' : ⟪affineResidual μ hQ u s hfin f, restrictedOne μ s hfin⟫_ℝ = 0 := by
    simpa only [affineCoordinateMap_apply, map_zero, one_smul, add_zero,
      affineResidual, sub_apply, ContinuousLinearMap.id_apply] using ho
  have hi' : ⟪restrictedOne μ s hfin, affineResidual μ hQ u s hfin f⟫_ℝ =
      ∫ x, affineResidual μ hQ u s hfin f x ∂μ.restrict s := by
    simpa [restrictedOne] using hi
  rw [← hi', real_inner_comm]
  exact ho'

/-- The residual is orthogonal to each original coordinate in `L²`. -/
theorem affineResidual_coordinate_inner (f : Lp ℝ 2 (μ.restrict s)) (i : Fin n) :
    ⟪affineResidual μ hQ u s hfin f,
      SobolevSpace.restrictLp μ hQ s (u i)⟫_ℝ = 0 := by
  have ho := affineProjection_orthogonal μ hQ u s hfin f 0
    (EuclideanSpace.single i 1)
  simpa only [affineCoordinateMap_apply, zero_smul, zero_add,
    sobolevColumnMap_single, affineResidual, sub_apply,
    ContinuousLinearMap.id_apply] using ho

/-- Uniform nondegeneracy of the value coordinates gives uniform bounds
for the coefficients of their least-squares fit. -/
theorem affineProjection_controlled_coefficients (f : Lp ℝ 2 (μ.restrict s))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ c v, |c| + ‖v‖ ≤ C * ‖affineCoordinateMap μ hQ u s hfin (c, v)‖) :
    ∃ c : ℝ, ∃ v : Euclidean n,
      affineProjection μ hQ u s hfin f = affineCoordinateMap μ hQ u s hfin (c, v) ∧
      |c| + ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨c, v, hcv⟩ := affineProjection_has_coefficients μ hQ u s hfin f
  change affineProjection μ hQ u s hfin f =
    affineCoordinateMap μ hQ u s hfin (c, v) at hcv
  refine ⟨c, v, hcv, ?_⟩
  have hb := hbound c v
  rw [← hcv] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (affineProjection_norm_le μ hQ u s hfin f) hC)

/-- Vanishing of an affine residual follows from affinity itself. This is
the final contradiction after Euclidean Euler rigidity in sharp projection. -/
theorem affineResidual_eq_zero_of_mem (f : Lp ℝ 2 (μ.restrict s))
    (hf : f ∈ affineCoordinateSpace μ hQ u s hfin) :
    affineResidual μ hQ u s hfin f = 0 := by
  have he := (affineCoordinateSpace μ hQ u s hfin).starProjection_eq_self_iff.mpr hf
  change f - affineProjection μ hQ u s hfin f = 0
  exact sub_eq_zero.mpr he.symm

end RegularPointCoordinates

end

end OAI
