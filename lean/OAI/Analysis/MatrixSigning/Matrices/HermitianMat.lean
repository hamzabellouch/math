import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def hermitianSubmodule (d : ℕ) : Submodule ℝ (Mat d) where
  carrier := {A | A.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' hA hB := hA.add hB
  smul_mem' r A hA := by
    change ((r : ℂ) • A).IsHermitian
    exact hA.smul (by change star (r : ℂ) = (r : ℂ); simp)

abbrev H (d : ℕ) := hermitianSubmodule d

variable {d : ℕ}

instance : FiniteDimensional ℝ (H d) := inferInstance

instance : IsUniformAddGroup (H d) := (H d).toAddSubgroup.isUniformAddGroup

instance : CompleteSpace (H d) := FiniteDimensional.complete ℝ (H d)

@[simp] theorem matrix_hermitian (A : H d) : (A : Mat d).IsHermitian := A.property

def one : H d := ⟨1, Matrix.isHermitian_one⟩

@[simp] theorem one_val : ((one : H d) : Mat d) = 1 := rfl

def realTrace (A : H d) : ℝ := (A.val.trace).re

def psdCone (d : ℕ) : ConvexCone ℝ (H d) where
  carrier := {A | (A : Mat d).PosSemidef}
  smul_mem' r hr A hA := by
    change ((r : ℂ) • (A : Mat d)).PosSemidef
    exact hA.smul (by simpa using hr.le)
  add_mem' A hA B hB := hA.add hB

@[simp] theorem mem_psdCone (A : H d) : A ∈ psdCone d ↔ (A : Mat d).PosSemidef := Iff.rfl

@[simp] theorem zero_mem_psdCone : (0 : H d) ∈ psdCone d := Matrix.PosSemidef.zero

@[simp] theorem one_mem_psdCone : (one : H d) ∈ psdCone d := Matrix.PosSemidef.one

section OperatorNorm
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem trace_mul_nonneg {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let : CStarAlgebra (Mat d) := {}
  have hs : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have ht := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hs.isHermitian.eq, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at ht
  exact (Complex.nonneg_iff.mp ht).1

theorem posDef_mem_interior [NeZero d] (A : H d) (hA : (A : Mat d).PosDef) :
    A ∈ interior (psdCone d : Set (H d)) := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨r, hr, hrA⟩ := (CFC.exists_pos_algebraMap_le_iff (A : Mat d) hA.isHermitian).mpr
    ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (A : Mat d)).mp hA.isStrictlyPositive)
  have hc : Continuous (fun B : H d => (B : Mat d) - (A : Mat d)) :=
    continuous_subtype_val.sub continuous_const
  have hn : Continuous (fun B : H d => ‖(B : Mat d) - (A : Mat d)‖) :=
    continuous_norm.comp hc
  have ho : IsOpen {B : H d | ‖(B : Mat d) - (A : Mat d)‖ < r} :=
    isOpen_lt hn continuous_const
  have hs : {B : H d | ‖(B : Mat d) - (A : Mat d)‖ < r} ⊆ (psdCone d : Set (H d)) := by
    intro B hB
    have hnorm : ‖(A : Mat d) - (B : Mat d)‖ < r := by
      rwa [norm_sub_rev]
    have hle : (A : Mat d) - (B : Mat d) ≤ (algebraMap ℝ (Mat d)) r :=
      (A.property.sub B.property).isSelfAdjoint.le_algebraMap_norm_self.trans
        (by
          change ((algebraMap ℝ (Mat d)) r - (algebraMap ℝ (Mat d)) ‖(A : Mat d) - (B : Mat d)‖).PosSemidef
          have hp := (Matrix.PosSemidef.one (n := Fin d) (R := ℂ)).smul
            (a := ((r - ‖(A : Mat d) - (B : Mat d)‖ : ℝ) : ℂ))
            (by exact_mod_cast sub_nonneg.mpr hnorm.le)
          convert hp using 1
          ext i j
          simp only [Algebra.algebraMap_eq_smul_one, Matrix.sub_apply,
            Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub]
          simp only [Complex.real_smul]
          ring)
    have hh := hle.trans hrA
    exact (show 0 ≤ (B : Mat d) by simpa using hh).posSemidef
  apply interior_maximal hs ho
  simpa using hr

end OperatorNorm

open scoped Matrix.Norms.Frobenius

def asL2 {d : ℕ} (A : Mat d) : PiLp 2 (fun _ : Fin d => EuclideanSpace ℂ (Fin d)) :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))

instance matrixInnerProduct (d : ℕ) : InnerProductSpace ℂ (Mat d) where
  inner A B := inner ℂ (asL2 A) (asL2 B)
  norm_sq_eq_re_inner A := norm_sq_eq_re_inner (asL2 A)
  conj_inner_symm A B := inner_conj_symm (asL2 A) (asL2 B)
  add_left A B C := by
    change inner ℂ (asL2 A + asL2 B) (asL2 C) = _
    exact inner_add_left _ _ _
  smul_left A B r := by
    change inner ℂ (r • asL2 A) (asL2 B) = _
    exact inner_smul_left _ _ _

instance matrixRealInnerProduct (d : ℕ) : InnerProductSpace ℝ (Mat d) :=
  InnerProductSpace.complexToReal

lemma inner_smul_leftH (A B : H d) (r : ℝ) :
    inner ℝ (r • A) B = r * inner ℝ A B := by
  exact real_inner_smul_left A B r

lemma inner_smul_rightH (A B : H d) (r : ℝ) :
    inner ℝ A (r • B) = r * inner ℝ A B := by
  exact real_inner_smul_right A B r

theorem matrix_inner (d : ℕ) (A B : Mat d) :
    inner ℂ A B = (B * Aᴴ).trace := by
  change inner ℂ (asL2 A) (asL2 B) = _
  simp only [asL2, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1

theorem inner_eq_trace (A B : H d) :
    inner ℝ A B = ((A : Mat d) * (B : Mat d)).trace.re := by
  change (inner ℂ (A : Mat d) (B : Mat d)).re = _
  rw [matrix_inner, A.property.eq, Matrix.trace_mul_comm]

@[simp] theorem inner_one (A : H d) : inner ℝ one A = realTrace A := by
  rw [inner_eq_trace, one_val, one_mul]
  rfl

@[simp] theorem inner_one' (A : H d) : inner ℝ A one = realTrace A := by
  rw [real_inner_comm]
  exact inner_one A

theorem inner_nonneg_of_psd (A B : H d) (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    0 ≤ inner ℝ A B := by
  rw [inner_eq_trace]
  exact trace_mul_nonneg hA hB

def rankOne (v : Fin d → ℂ) : H d :=
  ⟨Matrix.vecMulVec v (star v), (Matrix.posSemidef_vecMulVec_self_star v).isHermitian⟩

theorem rankOne_mem_psdCone (v : Fin d → ℂ) : rankOne v ∈ psdCone d :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem inner_rankOne (A : H d) (v : Fin d → ℂ) :
    inner ℝ A (rankOne v) = (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re := by
  rw [inner_eq_trace]
  change ((A : Mat d) * Matrix.vecMulVec v (star v)).trace.re = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem psd_of_inner_nonneg (A : H d)
    (h : ∀ B ∈ psdCone d, 0 ≤ inner ℝ A B) : A ∈ psdCone d := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨A.property, fun v => ?_⟩
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [inner_rankOne] using h (rankOne v) (rankOne_mem_psdCone v)
  · exact (A.property.im_star_dotProduct_mulVec_self v).symm

theorem positive_dual_matrix (p : StrongDual ℝ (H d))
    (hp : ∀ A ∈ psdCone d, 0 ≤ p A) :
    ∃ P : H d, P ∈ psdCone d ∧ ∀ A, p A = inner ℝ P A := by
  let b := stdOrthonormalBasis ℝ (H d)
  let P : H d := ∑ i, p (b i) • b i
  have he (A : H d) : inner ℝ P A = p A := by
    change inner ℝ (∑ i, p (b i) • b i : H d) A = p A
    rw [sum_inner]
    simp only [inner_smul_leftH]
    nth_rw 2 [← b.sum_repr' A]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul, smul_eq_mul, mul_comm]
  exact ⟨P, psd_of_inner_nonneg P (fun A hA => (he A).symm ▸ hp A hA),
    fun A => (he A).symm⟩

theorem isClosed_psdCone : IsClosed (psdCone d : Set (H d)) := by
  have he : (psdCone d : Set (H d)) =
      {A : H d | ∀ v : Fin d → ℂ, 0 ≤ (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re} := by
    ext A
    constructor
    · intro hA v
      exact hA.re_dotProduct_nonneg v
    · intro hA
      apply psd_of_inner_nonneg A

      have hp : (A : Mat d).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨A.property, fun v =>
          Complex.nonneg_iff.mpr ⟨hA v, (A.property.im_star_dotProduct_mulVec_self v).symm⟩⟩
      exact fun B hB => inner_nonneg_of_psd A B hp hB
  rw [he]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_le continuous_const
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    (continuous_subtype_val.matrix_mulVec continuous_const))

end
end CurrentKS.Hermitian

end OAI
