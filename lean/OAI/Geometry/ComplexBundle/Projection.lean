import OAI.Analysis.MatrixScaling.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

noncomputable section

/-! Projection frames and faithful normalized vector projections. -/

section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Topology NormedSpace
namespace Kaplansky
variable {d : ℕ}

/-- The actual one-dimensional subspace selected by a rank-one projection. -/
def projectionLine (p : projectionSpace d 1) : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  LinearMap.range (Matrix.toEuclideanLin p.val)

theorem projectionLine_finrank (p : projectionSpace d 1) : Module.finrank ℂ (projectionLine p) = 1 := by
  rw [projectionLine, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    ← Matrix.rank_eq_finrank_range_toLin]
  exact projectionSpace_rank p

/-- The projected coordinate vector supplies a local frame wherever nonzero. -/
def projectionColumn (p : projectionSpace d 1) (i : Fin d) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun j => p.val j i)

theorem projectionColumn_mem (p : projectionSpace d 1) (i : Fin d) :
    projectionColumn p i ∈ projectionLine p := by
  refine ⟨WithLp.toLp 2 (Pi.single i (1 : ℂ)), ?_⟩
  ext j
  simp [projectionColumn, Matrix.toLpLin_apply]

theorem continuous_projectionColumn (i : Fin d) : Continuous (fun p : projectionSpace d 1 => projectionColumn p i) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℂ)).comp
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)

theorem exists_projectionColumn_ne_zero (p : projectionSpace d 1) : ∃ i, projectionColumn p i ≠ 0 := by
  by_contra! h
  have hz : p.val = 0 := by
    ext j i
    have he := congrArg (fun v : EuclideanSpace ℂ (Fin d) => v j) (h i)
    exact he
  have hr := projectionSpace_rank p
  rw [hz, Matrix.rank_zero] at hr
  omega

def projectionChartSet (i : Fin d) : Set (projectionSpace d 1) := {p | projectionColumn p i ≠ 0}

theorem isOpen_projectionChartSet (i : Fin d) : IsOpen (projectionChartSet i) :=
  isOpen_ne.preimage (continuous_projectionColumn i)

def unitProjectionColumn (p : projectionSpace d 1) (i : Fin d) : EuclideanSpace ℂ (Fin d) :=
  NormedSpace.normalize (projectionColumn p i)

theorem unitProjectionColumn_norm (p : projectionSpace d 1) (i : Fin d)
    (hi : p ∈ projectionChartSet i) : ‖unitProjectionColumn p i‖ = 1 :=
  norm_normalize hi

theorem unitProjectionColumn_mem (p : projectionSpace d 1) (i : Fin d) :
    unitProjectionColumn p i ∈ projectionLine p := by
  unfold unitProjectionColumn NormedSpace.normalize
  exact (projectionLine p).smul_mem ((‖projectionColumn p i‖⁻¹ : ℝ) : ℂ) (projectionColumn_mem p i)

theorem continuousOn_unitProjectionColumn (i : Fin d) :
    ContinuousOn (fun p : projectionSpace d 1 => unitProjectionColumn p i) (projectionChartSet i) := by
  intro p hp
  apply ((continuous_projectionColumn i).norm.continuousWithinAt.inv₀ (norm_ne_zero_iff.mpr hp)).smul
    (continuous_projectionColumn i).continuousWithinAt

theorem projectionLine_eq_span (p : projectionSpace d 1) (i : Fin d)
    (hi : p ∈ projectionChartSet i) :
    projectionLine p = Submodule.span ℂ {unitProjectionColumn p i} :=
  eq_span_singleton_of_mem_of_finrank_eq_one (projectionLine_finrank p)
    (unitProjectionColumn_mem p i) (by intro h; simpa [h] using unitProjectionColumn_norm p i hi)

/-- The local frame gives the actual orthogonal coordinate formula on each line. -/
theorem unitProjectionColumn_reconstruct (p : projectionSpace d 1) (i : Fin d)
    (hi : p ∈ projectionChartSet i) (v : EuclideanSpace ℂ (Fin d)) (hv : v ∈ projectionLine p) :
    inner ℂ (unitProjectionColumn p i) v • unitProjectionColumn p i = v := by
  rw [projectionLine_eq_span p i hi] at hv
  obtain ⟨z,rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, unitProjectionColumn_norm p i hi]
  simp

end Kaplansky

end

section
open Matrix Topology
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

def vectorOuter (v : EuclideanSpace ℂ (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec (fun i => v i) (fun i => star (v i))

theorem vectorOuter_hermitian (v : EuclideanSpace ℂ (Fin d)) : (vectorOuter v).IsHermitian := by
  ext i j
  simp [vectorOuter, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, star_mul]

theorem unitVector_dot (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) :
    (fun i => star (v i)) ⬝ᵥ (fun i => v i) = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  rw [hv] at h
  change (∑ i, v i * star (v i)) = ((1 : ℝ)^2 : ℂ) at h
  simpa [dotProduct,mul_comm] using h

theorem vectorOuter_idempotent (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) :
    vectorOuter v * vectorOuter v = vectorOuter v := by
  unfold vectorOuter
  rw [Matrix.vecMulVec_mul_vecMulVec,unitVector_dot v hv,one_smul]

theorem vectorOuter_trace (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) :
    (vectorOuter v).trace = 1 := by
  rw [vectorOuter,Matrix.trace_vecMulVec,dotProduct_comm]
  exact unitVector_dot v hv

/-- The ordinary rank-one orthogonal projector of a unit vector. -/
def unitVectorProjection (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) : projectionSpace d 1 :=
  ⟨vectorOuter v, vectorOuter_hermitian v, vectorOuter_idempotent v hv,
    by rw [vectorOuter_trace v hv]; simp⟩

theorem continuous_vectorOuter : Continuous (vectorOuter (d := d)) := by
  apply continuous_matrix
  intro i j
  exact ((EuclideanSpace.proj i).continuous).mul ((EuclideanSpace.proj j).continuous.star)

theorem projection_toEuclideanLin_symmetricProjection (p : projectionSpace d 1) :
    (Matrix.toEuclideanLin p.val).IsSymmetricProjection := by
  refine ⟨?_,Matrix.isSymmetric_toEuclideanLin_iff.mpr p.property.1⟩
  change (Matrix.toEuclideanLin p.val).comp (Matrix.toEuclideanLin p.val) = _
  rw [← Matrix.toLpLin_mul_same,p.property.2.1]

theorem projectionLine_injective : Function.Injective (projectionLine (d := d)) := by
  intro p q h
  let f : Submodule ℂ (EuclideanSpace ℂ (Fin d)) →
      (EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) := fun U => U.starProjection
  obtain ⟨_,hp⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    (projection_toEuclideanLin_symmetricProjection p)
  obtain ⟨_,hq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    (projection_toEuclideanLin_symmetricProjection q)
  apply Subtype.ext
  apply Matrix.toEuclideanLin.injective
  calc
    Matrix.toEuclideanLin p.val = f (projectionLine p) := hp
    _ = f (projectionLine q) := congrArg f h
    _ = Matrix.toEuclideanLin q.val := hq.symm

theorem vectorOuter_toEuclideanLin (v : EuclideanSpace ℂ (Fin d)) :
    Matrix.toEuclideanLin (vectorOuter v) = (InnerProductSpace.rankOne ℂ v v).toLinearMap := by
  change Matrix.toEuclideanLin (Matrix.vecMulVec v (star v)) = _
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne,LinearEquiv.apply_symm_apply]

theorem unitVectorProjection_line (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) :
    projectionLine (unitVectorProjection v hv) = Submodule.span ℂ {v} := by
  change LinearMap.range (Matrix.toEuclideanLin (vectorOuter v)) = _
  rw [vectorOuter_toEuclideanLin]
  ext w
  constructor
  · rintro ⟨z,rfl⟩
    exact (Submodule.span ℂ {v}).smul_mem (inner ℂ v z) (Submodule.subset_span (Set.mem_singleton v))
  · intro hw
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨c • v, ?_⟩
    simp [InnerProductSpace.rankOne_apply,inner_self_eq_norm_sq_to_K,hv]

end Kaplansky

end

open Matrix Topology NormedSpace
open scoped ComplexOrder Matrix.Norms.L2Operator
namespace Kaplansky
variable {d : ℕ}

def nonzeroVectorProjection (v : EuclideanSpace ℂ (Fin d)) (hv : v≠0) : projectionSpace d 1 :=
  unitVectorProjection (normalize v) (norm_normalize hv)

theorem nonzeroVectorProjection_line (v : EuclideanSpace ℂ (Fin d)) (hv : v≠0) :
    projectionLine (nonzeroVectorProjection v hv) = Submodule.span ℂ {v} := by
  rw [nonzeroVectorProjection,unitVectorProjection_line]
  change Submodule.span ℂ {((‖v‖⁻¹ : ℝ) : ℂ) • v} = _
  apply Submodule.span_singleton_smul_eq
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hv)

theorem continuousOn_normalizedOuter :
    ContinuousOn (fun v : EuclideanSpace ℂ (Fin d) => vectorOuter (normalize v)) {v | v≠0} := by
  apply continuous_vectorOuter.comp_continuousOn
  intro v hv
  exact (continuousWithinAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hv)).smul continuousWithinAt_id

/-- The canonical rank-one projection is continuous in a nonzero vector. -/
theorem continuous_nonzeroVectorProjection :
    Continuous (fun v : {v : EuclideanSpace ℂ (Fin d) // v≠0} => nonzeroVectorProjection v.val v.property) :=
  (continuousOn_iff_continuous_domRestrict.mp continuousOn_normalizedOuter).subtype_mk _

end Kaplansky

end

end OAI
