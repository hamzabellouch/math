import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem outer_toEuclideanCLM {n : ℕ} (v : Vec n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (outer v) =
      InnerProductSpace.rankOne ℝ v v := by
  have h : Matrix.toEuclideanLin.symm
      (InnerProductSpace.rankOne ℝ v v).toLinearMap = outer v := by
    rw [InnerProductSpace.symm_toEuclideanLin_rankOne]
    ext i j
    simp [outer, Matrix.vecMulVec_apply]
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (outer v) x = _
  rw [← h, LinearEquiv.apply_symm_apply]
  rfl

theorem outer_mul_self {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) :
    outer v * outer v = outer v := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).injective
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (outer v * outer v) =
    Matrix.toEuclideanCLM (𝕜 := ℝ) (outer v)
  rw [map_mul, outer_toEuclideanCLM]
  exact InnerProductSpace.isIdempotentElem_rankOne_self hv

theorem outer_isStarProjection {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) :
    IsStarProjection (outer v) := ⟨outer_mul_self v hv, (outerSym v).property⟩

theorem one_sub_outer_posSemidef {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) :
    (1 - outer v).PosSemidef := (outer_isStarProjection v hv).one_sub.nonneg.posSemidef

theorem norm_outer_unit {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) : ‖outer v‖ = 1 := by
  rw [Matrix.cstar_norm_def, outer_toEuclideanCLM, InnerProductSpace.norm_rankOne, hv,
    mul_one]

theorem kernelProjection_one_sub_of_isStarProjection {n : ℕ} (P : Mat n ℝ)
    (hP : IsStarProjection P) : kernelProjection (1 - P) = P := by
  let φ := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
  have hp : IsStarProjection (φ P) := hP.map φ
  have hrange : (φ P).range = (φ (1 - P)).ker := by
    rw [map_sub, map_one]
    exact LinearMap.IsIdempotentElem.range_eq_ker_one_sub
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp.isIdempotentElem)
  have hproj : φ P = (φ (1 - P)).ker.starProjection := by
    apply (ContinuousLinearMap.IsStarProjection.ext_iff hp
      (isStarProjection_starProjection (U := (φ (1 - P)).ker))).mpr
    rw [Submodule.range_starProjection]
    exact hrange
  apply φ.injective
  change φ (kernelProjection (1 - P)) = φ P
  rw [hproj]
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (kernelProjection (1 - P)) x = _
  rw [kernelProjection, LinearEquiv.apply_symm_apply]
  rfl

theorem kernelProjection_one_sub_outer {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) :
    kernelProjection (1 - outer v) = outer v :=
  kernelProjection_one_sub_of_isStarProjection (outer v) (outer_isStarProjection v hv)

theorem outer_mul_mul_outer {n : ℕ} (u : Vec n) (A : Mat n ℝ) :
    outer u * A * outer u =
      (dotProduct (fun i => u i) (A *ᵥ fun i => u i)) • outer u := by
  change Matrix.vecMulVec (fun i => u i) (fun i => u i) * A *
    Matrix.vecMulVec (fun i => u i) (fun i => u i) = _
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    outer, Matrix.dotProduct_mulVec]
  ring

end Paper256

end

end OAI
