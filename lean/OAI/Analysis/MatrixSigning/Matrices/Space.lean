import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.HermitianMat

namespace OAI

open Matrix

namespace CurrentKS.HermitianCoordinates
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators Matrix.Norms.Frobenius

variable {d : ℕ}
local instance : NormedAddCommGroup (H d) := inferInstance
local instance : NormedSpace ℝ (H d) := inferInstance

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)
local instance : NormedAddCommGroup (Space d) := inferInstance
local instance : NormedSpace ℝ (Space d) := inferInstance

def decode (x : Fin d × Fin d → ℝ) : Mat d := fun i j =>
  ⟨x (min i j,max i j),if i < j then x (j,i) else if j < i then -x (i,j) else 0⟩

def encode (A : H d) : Fin d × Fin d → ℝ := fun p =>
  if p.1 ≤ p.2 then (A.val p.1 p.2).re else (A.val p.2 p.1).im

lemma decode_hermitian (x : Fin d × Fin d → ℝ) : (decode x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  apply Complex.ext
  · simp [decode,min_comm,max_comm]
  · simp only [decode,Complex.star_def,Complex.conj_im]
    rcases lt_trichotomy i j with hij | hij | hji
    · simp [hij,not_lt.mpr hij.le]
    · subst j; simp
    · simp [hji,not_lt.mpr hji.le]

def assemble (x : Space d) : H d := ⟨decode x,decode_hermitian x⟩
def extract (A : H d) : Space d := WithLp.toLp 2 (encode A)

lemma extract_assemble (x : Space d) : extract (assemble x)=x := by
  ext p
  rcases p with ⟨i,j⟩
  by_cases hij : i ≤ j
  · simp [extract,assemble,encode,decode,hij]
  · have hji := lt_of_not_ge hij
    simp [extract,assemble,encode,decode,hij,hji]

lemma assemble_extract (A : H d) : assemble (extract A)=A := by
  apply Subtype.ext
  ext i j
  have hh := Matrix.IsHermitian.apply A.property i j
  have hd := Matrix.IsHermitian.apply A.property i i
  rcases lt_trichotomy i j with hij | hij | hji
  · apply Complex.ext <;>
      simp [assemble,extract,encode,decode,hij,hij.le,not_le.mpr hij]
  · subst j
    apply Complex.ext
    · simp [assemble,extract,encode,decode]
    · have him := congrArg Complex.im hd
      simp only [Complex.star_def,Complex.conj_im] at him
      simp [assemble,extract,encode,decode]
      linarith
  · apply Complex.ext
    · have hre := congrArg Complex.re hh
      simp only [Complex.star_def,Complex.conj_re] at hre
      simpa [assemble,extract,encode,decode,hji,hji.le,not_le.mpr hji,
        min_eq_right hji.le,max_eq_left hji.le] using hre
    · have him := congrArg Complex.im hh
      simp only [Complex.star_def,Complex.conj_im] at him
      simpa [assemble,extract,encode,decode,hji,hji.le,not_lt.mpr hji.le,
        not_le.mpr hji] using him

lemma decode_add (x y : Fin d × Fin d → ℝ) : decode (x+y)=decode x+decode y := by
  ext i j
  apply Complex.ext
  · simp [decode,Matrix.add_apply]
  · simp only [decode,Matrix.add_apply,Pi.add_apply,Complex.add_im]
    split_ifs <;> ring

lemma decode_smul (r : ℝ) (x : Fin d × Fin d → ℝ) : decode (r • x)=r • decode x := by
  ext i j
  apply Complex.ext
  · simp [decode,Matrix.smul_apply]
  · simp only [decode,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Complex.real_smul,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul]
    split_ifs <;> ring

def assembleLinear (d : ℕ) : Space d →ₗ[ℝ] H d where
  toFun := assemble
  map_add' x y := Subtype.ext (decode_add x y)
  map_smul' r x := Subtype.ext (decode_smul r x)

lemma norm_decode_entry (x : Fin d × Fin d → ℝ) (i j : Fin d) :
    ‖decode x i j‖^2 ≤ x (i,j)^2+x (j,i)^2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  rcases lt_trichotomy i j with hij | hij | hji
  · simp [decode,min_eq_left hij.le,max_eq_right hij.le,hij,pow_two]
  · subst j
    simp only [decode,min_self,max_self,lt_self_iff_false,ite_false]
    nlinarith [sq_nonneg (x (i,i))]
  · simp [decode,min_eq_right hji.le,max_eq_left hji.le,hji,not_lt.mpr hji.le,pow_two]
    ring_nf
    rfl

lemma norm_assemble_sq (x : Space d) : ‖assemble x‖^2 ≤ 2*‖x‖^2 := by
  have hm : ‖assemble x‖^2 = ∑ i : Fin d, ∑ j : Fin d, ‖decode x i j‖^2 := by
    change ‖asL2 (decode x)‖^2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [asL2,PiLp.toLp_apply,PiLp.norm_sq_eq_of_L2]
  rw [hm,PiLp.norm_sq_eq_of_L2]
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => norm_decode_entry x i j))
  have he : (∑ i : Fin d, ∑ j : Fin d, x (j,i)^2) = ∑ i : Fin d, ∑ j : Fin d, x (i,j)^2 :=
    Finset.sum_comm
  simpa only [Finset.sum_add_distrib,Fintype.sum_prod_type,Real.norm_eq_abs,sq_abs,
    two_mul,he] using hb

lemma norm_assemble (x : Space d) : ‖assemble x‖ ≤ 2*‖x‖ := by
  have h := norm_assemble_sq x
  nlinarith [norm_nonneg x,norm_nonneg (assemble x)]

private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

private local instance : TopologicalSpace (Space d) :=
  (inferInstance : NormedAddCommGroup (Space d)).toUniformSpace.toTopologicalSpace

def assembleCLM (d : ℕ) : Space d →L[ℝ] H d :=
  (assembleLinear d).mkContinuous 2 norm_assemble

lemma norm_assembleCLM : ‖(assembleCLM d : Space d →L[ℝ] H d)‖ ≤ (2:ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) norm_assemble

end
end CurrentKS.HermitianCoordinates

end OAI
