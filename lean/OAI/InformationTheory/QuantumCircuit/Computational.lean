import OAI.InformationTheory.QuantumCircuit.Toffoli
import OAI.InformationTheory.QuantumCircuit.Spectral

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma matrix_entry_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖ ≤ ‖A‖ := by
  classical
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  have h := A.l2_opNorm_mulVec v
  have he := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm (A *ᵥ v)) i
  have hv : ‖v‖=1 := by simp [v]
  rw [hv,mul_one] at h
  apply le_trans _ h
  simpa [v,Matrix.mulVec,dotProduct,Pi.single_apply] using he

lemma tensorMatrix_diagonal {N : ℕ} (f : Fin N → Bit → ℂ) :
    tensorMatrix (fun i => Matrix.diagonal (f i)) = Matrix.diagonal (fun x => ∏ i, f i (x i)) := by
  classical
  ext x y
  simp only [tensorMatrix,Matrix.diagonal_apply]
  by_cases hxy : x=y
  · subst y; simp
  · simp only [ite_eq_right hxy]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma rankOne_basis_diagonal (b : Bit) :
    rankOne (basisVector b) = Matrix.diagonal (fun x => if x=b then 1 else 0) := by
  ext x y
  rw [rankOne_basis,Matrix.diagonal_apply]
  split_ifs <;> simp_all

lemma one_sub_rankOne_basis (b : Bit) :
    1-rankOne (basisVector b) = rankOne (basisVector (1-b)) := by
  ext x y
  simp only [Matrix.sub_apply,Matrix.one_apply,rankOne_basis]
  fin_cases b <;> fin_cases x <;> fin_cases y <;> norm_num

/-- A full computational-basis count. -/
def computationalCount {N : ℕ} (z : Word N) : Count N where
  support := Finset.univ
  vector i := basisVector (z i)
  normalized i _ := basisVector_normalized (z i)

def basisProjection {N : ℕ} (z : Word N) : Operator N :=
  Matrix.diagonal (fun x => if x=z then 1 else 0)

lemma computationalCount_zero {N : ℕ} (z : Word N) : (computationalCount z).zero=basisProjection z := by
  classical
  simp only [Count.zero,computationalCount,Finset.mem_univ,ite_true,rankOne_basis_diagonal]
  rw [tensorMatrix_diagonal]
  congr 1
  funext x
  rw [Fintype.prod_boole]
  simp only [funext_iff]
  split_ifs <;> rfl

/-- Complement selected computational bits. -/
def flipWord {N : ℕ} (F : Finset (Fin N)) (z : Word N) : Word N :=
  fun i => if i ∈ F then 1-z i else z i

lemma flipWord_involutive {N : ℕ} (F : Finset (Fin N)) : Function.Involutive (flipWord F) := by
  intro z
  funext i
  simp only [flipWord]
  split_ifs
  · generalize z i = b
    fin_cases b <;> decide
  · rfl

lemma computationalCount_pattern {N : ℕ} (z : Word N) (F : Finset (Fin N)) :
    (computationalCount z).pattern F = basisProjection (flipWord F z) := by
  classical
  rw [← computationalCount_zero]
  simp only [Count.pattern,Count.zero,computationalCount,Finset.mem_univ,ite_true]
  congr 1
  funext i
  by_cases hi : i∈F
  · simp only [ite_eq_left hi,flipWord]
    exact one_sub_rankOne_basis (z i)
  · simp [hi,flipWord]

lemma basisProjection_mul_entry {N : ℕ} (z : Word N) (A : Operator N) (y : Word N) :
    (basisProjection z*A) z y = A z y := by
  classical
  simp [basisProjection,Matrix.diagonal_mul]

lemma mul_basisProjection_entry {N : ℕ} (z : Word N) (A : Operator N) (y : Word N) :
    (A*basisProjection z) y z = A y z := by
  classical
  simp [basisProjection,Matrix.mul_diagonal]

lemma high_entry_bound {N : ℕ} (B : Operator N) (z : Word N) (F : Finset (Fin N))
    {r : ℝ} (hr : r ≤ (F.card:ℝ)) :
    ‖B (flipWord F z) z‖ ≤ ‖(computationalCount z).high r*B*(computationalCount z).zero‖ := by
  let y := flipWord F z
  have habs := (computationalCount z).high_mul_pattern F (Finset.subset_univ F) r
  rw [ite_eq_left hr,computationalCount_pattern] at habs
  have hleft : basisProjection y*(computationalCount z).high r = basisProjection y := by
    have h := congrArg star habs
    rw [star_mul, ((computationalCount z).high_projection r).isSelfAdjoint.star_eq] at h
    change star (basisProjection y)*(computationalCount z).high r = star (basisProjection y) at h
    simpa only [← computationalCount_zero,
      (computationalCount y).zero_projection.isSelfAdjoint.star_eq,
      ((computationalCount z).high_projection r).isSelfAdjoint.star_eq] using h
  have heq : ((computationalCount z).high r*B*basisProjection z) y z = B y z := by
    rw [← basisProjection_mul_entry y ((computationalCount z).high r*B*basisProjection z) z]
    rw [← mul_assoc,← mul_assoc,hleft,mul_basisProjection_entry,basisProjection_mul_entry]
  rw [computationalCount_zero]
  exact heq ▸ matrix_entry_norm_le ((computationalCount z).high r*B*basisProjection z) y z

/-- Input positions; ancillas occupy the other positions. -/
def inputSet (n N : ℕ) : Finset (Fin N) := Finset.univ.filter (fun i => i.val<n)

lemma inputSet_card {n N : ℕ} (hnN : n ≤ N) : (inputSet n N).card=n := by
  rw [inputSet,Fin.card_filter_val_lt,min_eq_right hnN]

/-- The real character of a single bit. -/
def bitSign (b : Bit) : ℝ := if b=0 then 1 else -1

def bitX : QubitOperator := !![0,1;1,0]
def bitZ : QubitOperator := Matrix.diagonal (fun b => (bitSign b:ℂ))
def bitH : QubitOperator := !![(halfScale:ℂ),(halfScale:ℂ);(halfScale:ℂ),-(halfScale:ℂ)]

lemma halfScale_complex_sq : (halfScale:ℂ)^2=1/2 := by
  rw [← Complex.ofReal_pow,halfScale_sq]
  norm_num

lemma bitH_star : star bitH=bitH := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bitH,Matrix.star_apply]

lemma bitH_sq : bitH*bitH=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitH,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals linear_combination 2*halfScale_complex_sq

lemma bitH_unitary : bitH ∈ unitary QubitOperator := by
  simp only [Unitary.mem_iff,bitH_star,bitH_sq,and_self]

def hadamardGate : Matrix.unitaryGroup Bit ℂ := ⟨bitH,bitH_unitary⟩

lemma bitH_X_H : bitH*bitX*bitH=bitZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitH,bitX,bitZ,bitSign,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals first | linear_combination 2*halfScale_complex_sq | linear_combination -2*halfScale_complex_sq

def inputHadamard (n N : ℕ) : LocalLayer N := fun i => if i.val<n then hadamardGate else 1

def inputFlip (n N : ℕ) : Operator N := tensorMatrix (fun i => if i.val<n then bitX else 1)
def inputPhase (n N : ℕ) : Operator N := tensorMatrix (fun i => if i.val<n then bitZ else 1)

lemma inputHadamard_star (n N : ℕ) : star (localMatrix (inputHadamard n N)) =
    localMatrix (inputHadamard n N) := by
  rw [localMatrix_star]
  congr 1
  funext i
  apply Subtype.ext
  by_cases hi : i.val<n
  · simp only [inputHadamard,ite_eq_left hi,Unitary.coe_star,hadamardGate]
    exact bitH_star
  · simp [inputHadamard,hi]

lemma inputHadamard_flip (n N : ℕ) :
    localMatrix (inputHadamard n N)*inputFlip n N*localMatrix (inputHadamard n N) = inputPhase n N := by
  unfold localMatrix inputFlip inputPhase
  rw [tensorMatrix_mul,tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i.val<n
  · simpa only [inputHadamard,ite_eq_left hi,hadamardGate] using bitH_X_H
  · simp [inputHadamard,hi]

end QAC

end

end OAI
