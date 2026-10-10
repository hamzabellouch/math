import OAI.Probability.InvariantIsing.Haar.MatrixRotation

namespace OAI

/-! Smooth coordinate-plane rotations for the finite Haar Ward calculation. -/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

/-- Generator with xᵢ'=xⱼ and xⱼ'=-xᵢ. -/
def planeGenerator {N : ℕ} (i j : Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.single i j 1 - Matrix.single j i 1

lemma planeGenerator_skew {N : ℕ} (i j : Fin N) :
    planeGenerator i j ∈ skewAdjoint (Matrix (Fin N) (Fin N) ℝ) := by
  rw [skewAdjoint.mem_iff]
  simp [planeGenerator, Matrix.star_eq_conjTranspose]

/-- The exponential of the plane generator is orthogonal. -/
def planeRotation {N : ℕ} (i j : Fin N) (t : ℝ) : Orthogonal N :=
  ⟨NormedSpace.exp (t • planeGenerator i j),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (by simpa only [skewAdjoint.mem_iff, star_smul, star_trivial, smul_neg] using
        congrArg (fun M => t • M) (skewAdjoint.mem_iff.mp (planeGenerator_skew i j)))⟩

@[simp] lemma planeRotation_zero {N : ℕ} (i j : Fin N) : planeRotation i j 0 = 1 := by
  apply Subtype.ext
  simp [planeRotation]

lemma planeGenerator_mulVec {N : ℕ} (i j k : Fin N) (v : Fin N → ℝ) :
    (planeGenerator i j *ᵥ v) k =
      (if k = i then v j else 0) - (if k = j then v i else 0) := by
  simp [planeGenerator, Matrix.sub_mulVec, Matrix.single_mulVec, Function.update_apply, eq_comm]

/-- Coordinate evaluation of matrix-vector multiplication as a continuous
linear functional, with the Frobenius norm used only for the exponential. -/
def matrixVectorCoordinate {N : ℕ} (k : Fin N) (v : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
  (show Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ from
    { toFun := fun M => (M *ᵥ v) k
      map_add' := by intros; simp [Matrix.add_mulVec]
      map_smul' := by intros; simp [Matrix.smul_mulVec] }).toContinuousLinearMap

/-- The coordinate derivative along a genuine Haar-preserving plane rotation. -/
lemma hasDerivAt_planeRotation_coordinate {N : ℕ} (i j k : Fin N)
    (U : Orthogonal N) (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    HasDerivAt (fun s => matrixRotation (planeRotation i j s * U) v k)
      ((if k = i then matrixRotation (planeRotation i j t * U) v j else 0) -
        (if k = j then matrixRotation (planeRotation i j t * U) v i else 0)) t := by
  let A := planeGenerator i j
  let ev := matrixVectorCoordinate k v.ofLp
  have he := (hasDerivAt_exp_smul_const' A t).mul_const
    (U : Matrix (Fin N) (Fin N) ℝ)
  have hd := ev.hasFDerivAt.comp_hasDerivAt t he
  convert hd using 1
  · rfl
  · change _ = ((A * NormedSpace.exp (t • A) * (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ
        v.ofLp) k
    rw [mul_assoc, ← Matrix.mulVec_mulVec]
    exact (planeGenerator_mulVec i j k
      ((NormedSpace.exp (t • A) * (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ v.ofLp)).symm

lemma hasDerivAt_planeRotation_energy {N : ℕ} (i j : Fin N)
    (U : Orthogonal N) (eig : Fin N → ℝ) (σ : Spin N) (t : ℝ) :
    HasDerivAt (fun s => rotatedEnergy eig (matrixRotation (planeRotation i j s * U)) σ)
      ((eig i - eig j) * matrixRotation (planeRotation i j t * U) (spinVector σ) i *
        matrixRotation (planeRotation i j t * U) (spinVector σ) j) t := by
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((hasDerivAt_planeRotation_coordinate i j k U (spinVector σ) t).pow 2).const_mul
      (eig k))).const_mul (1 / 2 : ℝ)
  convert hd using 1
  · rfl
  · simp only [Nat.cast_ofNat, mul_sub, mul_ite, mul_zero, sub_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

end InvariantIsing

end

end OAI
