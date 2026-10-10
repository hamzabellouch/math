import OAI.Combinatorics.EuclideanRamsey.DifferentialSplitting

namespace OAI

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace EuclideanRamsey
lemma exists_positive_shift {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.IsSymm) :
    ∃ L : ℝ, 0 < L ∧ (L • (1 : Matrix (Fin k) (Fin k) ℝ) + C).PosDef := by
  by_cases hk : k = 0
  · subst k
    exact ⟨1, zero_lt_one, by convert (Matrix.PosDef.one : (1 : Matrix (Fin 0) (Fin 0) ℝ).PosDef) using 1; exact Subsingleton.elim _ _⟩
  let : NeZero k := ⟨hk⟩
  have hh : C.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hC
  have h : -(algebraMap ℝ (Matrix (Fin k) (Fin k) ℝ) ‖C‖) ≤ C :=
    by
      rw [neg_le]
      exact le_algebraMap_of_spectrum_le (fun r hr => (Real.le_norm_self r).trans
        (by simpa using spectrum.norm_le_norm_of_mem hr)) hh.neg.isSelfAdjoint
  have h' : (‖C‖ • (1 : Matrix (Fin k) (Fin k) ℝ) + C).PosSemidef := by
    simpa [Matrix.le_iff, Algebra.algebraMap_eq_smul_one, add_comm] using h
  refine ⟨1+‖C‖, by positivity, ?_⟩
  convert Matrix.PosDef.one.add_posSemidef h' using 1 ; simp [add_smul, add_assoc]

lemma covariance_splitting {k d : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ) (hC : C.IsSymm)
    (hU : U * C * U.transpose = 1) :
    let R := C * U.transpose
    let Z := 1 - R * U
    U * R = 1 ∧ U * Z = 0 ∧ C = R * R.transpose + Z * C * Z.transpose := by
  dsimp only
  let R := C * U.transpose
  have hR : U * R = 1 := by simpa only [R, ← Matrix.mul_assoc] using hU
  have hRt : R.transpose = U * C := by simp only [R, Matrix.transpose_mul,
    Matrix.transpose_transpose, hC.eq]
  have hRR : R.transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  refine ⟨hR, ?_, ?_⟩
  · change U * (1 - R * U) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]
  · change C = R * R.transpose + (1 - R * U) * C * (1 - R * U).transpose
    have ht : (1 - R * U).transpose = 1 - U.transpose * R.transpose := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
    have h1 : R * U * C = R * R.transpose := by rw [hRt, Matrix.mul_assoc]
    have h2 : C * (U.transpose * R.transpose) = R * R.transpose := by
      rw [← Matrix.mul_assoc]
    have h3 : R * R.transpose * (U.transpose * R.transpose) = R * R.transpose := by
      rw [ Matrix.mul_assoc, ← Matrix.mul_assoc R.transpose, hRR, Matrix.one_mul]
    simp only [ht, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      h1, h2, h3]
    abel

lemma positive_joint_pushforward {k d : ℕ} (R : Matrix (Fin k) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ) (Z : Matrix (Fin k) (Fin k) ℝ)
    (hRU : R * U + Z = 1) (A : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin k) (Fin k) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (R * A * R.transpose + Z * B * Z.transpose).PosDef := by
  have hs : (R * A * R.transpose + Z * B * Z.transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (isHermitian_mul_mul_conjTranspose R hA.isHermitian).add
        (isHermitian_mul_mul_conjTranspose Z hB.isHermitian)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  have hj : R.transpose *ᵥ x ≠ 0 ∨ Z.transpose *ᵥ x ≠ 0 := by
    by_contra hh
    push Not at hh
    have he := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M.transpose *ᵥ x) hRU
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hh.1, hh.2,
      Matrix.mulVec_zero, add_zero] at he
    exact hx he.symm
  have ha : 0 ≤ (R.transpose *ᵥ x) ⬝ᵥ (A *ᵥ (R.transpose *ᵥ x)) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (R.transpose *ᵥ x)
  have hb : 0 ≤ (Z.transpose *ᵥ x) ⬝ᵥ (B *ᵥ (Z.transpose *ᵥ x)) := by
    simpa using hB.posSemidef.dotProduct_mulVec_nonneg (Z.transpose *ᵥ x)
  have hpos : 0 < (R.transpose *ᵥ x) ⬝ᵥ (A *ᵥ (R.transpose *ᵥ x)) +
      (Z.transpose *ᵥ x) ⬝ᵥ (B *ᵥ (Z.transpose *ᵥ x)) := by
    rcases hj with hj | hj
    · exact add_pos_of_pos_of_nonneg (by simpa using hA.dotProduct_mulVec_pos hj) hb
    · exact add_pos_of_nonneg_of_pos ha (by simpa using hB.dotProduct_mulVec_pos hj)
  have heq {n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
      x ⬝ᵥ ((M * D * M.transpose) *ᵥ x) =
        (M.transpose *ᵥ x) ⬝ᵥ (D *ᵥ (M.transpose *ᵥ x)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec x M]
    have ht : x ᵥ* M = M.transpose *ᵥ x := by
      simpa using Matrix.vecMul_transpose M.transpose x
    rw [ht]
  simpa only [star_trivial, Matrix.add_mulVec, dotProduct_add, heq] using hpos

theorem exists_small_covariance {k d : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ) (hC : C.IsSymm)
    (hU : U * C * U.transpose = 1) {η : ℝ} (hη : 0 < η) :
    ∃ S : Matrix (Fin k) (Fin k) ℝ, S.PosDef ∧ (S + C).PosDef ∧
      (U * S * U.transpose).trace < η := by
  let R := C * U.transpose
  let Z := 1 - R * U
  obtain ⟨hR, hZ, hsplit⟩ := covariance_splitting C U hC hU
  change U * R = 1 at hR
  change U * Z = 0 at hZ
  change C = R * R.transpose + Z * C * Z.transpose at hsplit
  have hj : R * U + Z = 1 := by dsimp [Z]; abel
  obtain ⟨L, hL, hLC⟩ := exists_positive_shift C hC
  let ε : ℝ := η / (2 * (d + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let S := R * (ε • (1 : Matrix (Fin d) (Fin d) ℝ)) * R.transpose +
    Z * (L • (1 : Matrix (Fin k) (Fin k) ℝ)) * Z.transpose
  refine ⟨S, positive_joint_pushforward R U Z hj _ _
    (Matrix.PosDef.one.smul hε) (Matrix.PosDef.one.smul hL), ?_, ?_⟩
  · have heq : S + C = R * ((ε + 1) • (1 : Matrix (Fin d) (Fin d) ℝ)) * R.transpose +
        Z * (L • (1 : Matrix (Fin k) (Fin k) ℝ) + C) * Z.transpose := by
      conv_lhs => rw [hsplit]
      simp only [S, add_smul, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
      abel
    rw [heq]
    exact positive_joint_pushforward R U Z hj _ _
      (Matrix.PosDef.one.smul (by linarith)) hLC
  · have heq {n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ)
        (A : Matrix (Fin n) (Fin n) ℝ) :
        U * (M * A * M.transpose) * U.transpose =
          (U * M) * A * (U * M).transpose := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have hcov : U * S * U.transpose = ε • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      dsimp only [S]
      rw [Matrix.mul_add, Matrix.add_mul, heq, heq, hR, hZ]
      simp
    rw [hcov, Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    dsimp [ε]
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (d+1))).mpr
    nlinarith

end EuclideanRamsey

open scoped BigOperators
open MeasureTheory Matrix
namespace EuclideanRamsey

def stencilDifferential {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (b : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ j, ∑ l, C j l *
    iteratedFDeriv ℝ 2 b x ![Pi.single j 1, Pi.single l 1]

def gradientWeight {k d : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ a, (∑ j, U a j * x j)^2

lemma gradientWeight_nonneg {k d : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (x : Fin k → ℝ) :
    0 ≤ gradientWeight U x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def CompactSmoothing : Prop :=
  ∀ (k d : ℕ), 1 ≤ d → ∀ (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ), C.IsSymm → U * C * U.transpose = 1 →
    ∀ η : ℝ, 0 < η → ∃ b : (Fin k → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ (∀ x, 0 ≤ b x) ∧
      0 < ∫ x, b x ∧
      (∫ x, max (-(stencilDifferential C b x)) 0 * gradientWeight U x) < η * ∫ x, b x

end EuclideanRamsey
namespace EuclideanRamsey
open MeasureTheory Matrix
open scoped BigOperators

theorem compact_smoothing : CompactSmoothing := by
  intro k d hd C U hC hU η hη
  let R := C * U.transpose
  let Z : Matrix (Fin k) (Fin k) ℝ := 1-R*U
  obtain ⟨hUR,hUZ,hsplit⟩ := covariance_splitting C U hC hU
  change U*R=1 at hUR
  change U*Z=0 at hUZ
  change C=R*R.transpose+Z*C*Z.transpose at hsplit
  let H := EuclideanSpace ℝ (Fin d)
  let eH : H ≃ₗ[ℝ] (Fin d → ℝ) := (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv
  let u : (Fin k → ℝ) →ₗ[ℝ] H := eH.symm.toLinearMap.comp (Matrix.toLin' U)
  let r : H →ₗ[ℝ] (Fin k → ℝ) := (Matrix.toLin' R).comp eH.toLinearMap
  have hur : u.comp r = LinearMap.id := by
    apply LinearMap.ext
    intro y
    simp only [u,r,LinearMap.comp_apply,Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hUR, Matrix.one_mulVec]
    exact eH.symm_apply_apply y
  let V := LinearMap.ker u
  let e : (Fin k → ℝ) ≃L[ℝ] H×V := (rightInverseSplit u r hur).toContinuousLinearEquiv
  let eh : OrthonormalBasis (Fin d) ℝ H := EuclideanSpace.basisFun (Fin d) ℝ
  have hRv (j : Fin d) : r (eh j) = fun l => R l j := by
    change R.mulVec (eH (eh j)) = _
    have h : eH (eh j) = Pi.single j 1 := by
      change ((EuclideanSpace.basisFun (Fin d) ℝ) j).ofLp = _
      rw [EuclideanSpace.basisFun_apply]
      rfl
    rw [h, Matrix.mulVec_single]
    simp
    rfl
  have hZv (j : Fin k) : (fun l => Z l j) ∈ LinearMap.ker u := by
    rw [LinearMap.mem_ker]
    change eH.symm (U.mulVec (fun l => Z l j)) = 0
    have h : U.mulVec (fun l => Z l j) = 0 := by
      ext a
      change (U*Z) a j = 0
      rw [hUZ]; rfl
    rw [h,map_zero]
  let z : Fin k → V := fun j => ⟨fun l => Z l j,hZv j⟩
  have hR (j : Fin d) : e (fun l => R l j) = (eh j,0) := by
    rw [← hRv]
    exact rightInverseSplit_apply_R u r hur (eh j)
  have hZ (j : Fin k) : e (fun l => Z l j) = (0,z j) := by
    apply Prod.ext
    · exact hZv j
    · apply Subtype.ext
      change (fun l => Z l j) - r (u (fun l => Z l j)) = _
      rw [show u (fun l => Z l j) = 0 from hZv j,map_zero,sub_zero]
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  have hn : 1 ≤ Module.finrank ℝ H := by simpa [H] using hd
  obtain ⟨b,hbs,hbk,hbp,hbm,hsmall⟩ := exists_split_smoothing hn C R Z hsplit e eh z hR hZ hη
  refine ⟨b,hbs,hbk,hbp,hbm,?_⟩
  have hw (x : Fin k → ℝ) : ‖(e x).1‖^2 = gradientWeight U x := by
    change ‖eH.symm (U.mulVec x)‖^2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hop (x : Fin k → ℝ) : secondOperator C (fun j => Pi.single j 1) b x =
      stencilDifferential C b x := by simp only [secondOperator,stencilDifferential,hessianB_eq]
  simpa only [hw,hop] using hsmall

end EuclideanRamsey

end

end OAI
