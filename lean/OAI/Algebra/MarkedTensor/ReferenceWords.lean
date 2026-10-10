import Mathlib
import OAI.Algebra.MarkedTensor.AdjointCoordinates

namespace OAI

/-! Finite rational reference words whose adjoint actions span all endomorphisms. -/

noncomputable section
open scoped BigOperators commutatorElement
open Matrix

namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators

 
def referenceGenerator : Fin 3 → SpecialLinearGroup (Fin 2) ℚ := ![
  ⟨!![2,0;0,1/2], by norm_num [Matrix.det_fin_two]⟩,
  ⟨!![1,1;0,1], by norm_num [Matrix.det_fin_two]⟩,
  ⟨!![1,0;1,1], by norm_num [Matrix.det_fin_two]⟩]

def referenceRho : FreeGroup (Fin 3) →* SpecialLinearGroup (Fin 2) ℚ :=
  FreeGroup.lift referenceGenerator

def shortWords : Set (FreeGroup (Fin 3)) := {g | FreeGroup.norm g ≤ 5}

def spanningWord : Fin 9 → FreeGroup (Fin 3) := ![1,FreeGroup.of 0,
  FreeGroup.of 0 * FreeGroup.of 0,FreeGroup.of 1,FreeGroup.of 2,
  FreeGroup.of 1 * FreeGroup.of 0,FreeGroup.of 2 * FreeGroup.of 0,
  FreeGroup.of 0 * FreeGroup.of 1,FreeGroup.of 0 * FreeGroup.of 2]

lemma spanningWord_mem (i : Fin 9) : spanningWord i ∈ shortWords := by
  have hm (i j : Fin 3) : FreeGroup.norm (FreeGroup.of i * FreeGroup.of j) ≤ 5 :=
    (FreeGroup.norm_mul_le _ _).trans (by simp)
  fin_cases i <;> simp [spanningWord, shortWords,hm]

def spanningMatrix : Fin 9 → Matrix (Fin 3) (Fin 3) ℚ := ![
!![1,0,0; 0,1,0; 0,0,1],
!![4,0,0; 0,1,0; 0,0,(1/4)],
!![16,0,0; 0,1,0; 0,0,(1/16)],
!![1,-2,-1; 0,1,1; 0,0,1],
!![1,0,0; -1,1,0; -1,2,1],
!![4,-2,(-1/4); 0,1,(1/4); 0,0,(1/4)],
!![4,0,0; -4,1,0; -4,2,(1/4)],
!![4,-8,-4; 0,1,1; 0,0,(1/4)],
!![4,0,0; -1,1,0; (-1/4),(1/2),(1/4)]]

@[simp] lemma spanningMatrix_at_0 : spanningMatrix 0 = !![1,0,0; 0,1,0; 0,0,1] := rfl
@[simp] lemma spanningWord_at_0 : spanningWord 0 = 1 := rfl
@[simp] lemma spanningMatrix_at_1 : spanningMatrix 1 = !![4,0,0; 0,1,0; 0,0,(1/4)] := rfl
@[simp] lemma spanningWord_at_1 : spanningWord 1 = FreeGroup.of 0 := rfl
@[simp] lemma spanningMatrix_at_2 : spanningMatrix 2 = !![16,0,0; 0,1,0; 0,0,(1/16)] := rfl
@[simp] lemma spanningWord_at_2 : spanningWord 2 = FreeGroup.of 0 * FreeGroup.of 0 := rfl
@[simp] lemma spanningMatrix_at_3 : spanningMatrix 3 = !![1,-2,-1; 0,1,1; 0,0,1] := rfl
@[simp] lemma spanningWord_at_3 : spanningWord 3 = FreeGroup.of 1 := rfl
@[simp] lemma spanningMatrix_at_4 : spanningMatrix 4 = !![1,0,0; -1,1,0; -1,2,1] := rfl
@[simp] lemma spanningWord_at_4 : spanningWord 4 = FreeGroup.of 2 := rfl
@[simp] lemma spanningMatrix_at_5 : spanningMatrix 5 = !![4,-2,(-1/4); 0,1,(1/4); 0,0,(1/4)] := rfl
@[simp] lemma spanningWord_at_5 : spanningWord 5 = FreeGroup.of 1 * FreeGroup.of 0 := rfl
@[simp] lemma spanningMatrix_at_6 : spanningMatrix 6 = !![4,0,0; -4,1,0; -4,2,(1/4)] := rfl
@[simp] lemma spanningWord_at_6 : spanningWord 6 = FreeGroup.of 2 * FreeGroup.of 0 := rfl
@[simp] lemma spanningMatrix_at_7 : spanningMatrix 7 = !![4,-8,-4; 0,1,1; 0,0,(1/4)] := rfl
@[simp] lemma spanningWord_at_7 : spanningWord 7 = FreeGroup.of 0 * FreeGroup.of 1 := rfl
@[simp] lemma spanningMatrix_at_8 : spanningMatrix 8 = !![4,0,0; -1,1,0; (-1/4),(1/2),(1/4)] := rfl
@[simp] lemma spanningWord_at_8 : spanningWord 8 = FreeGroup.of 0 * FreeGroup.of 2 := rfl

@[simp] lemma referenceRho_of (i : Fin 3) : referenceRho (FreeGroup.of i) = referenceGenerator i := by simp [referenceRho]

@[simp] lemma reference_mat_0 : mat (referenceGenerator 0) = !![(2:ℚ),0;0,1/2] := rfl
@[simp] lemma reference_mat_1 : mat (referenceGenerator 1) = !![(1:ℚ),1;0,1] := rfl
@[simp] lemma reference_mat_2 : mat (referenceGenerator 2) = !![(1:ℚ),0;1,1] := rfl
lemma reference_mat_inv (g : SpecialLinearGroup (Fin 2) ℚ) :
    mat g⁻¹ = Matrix.adjugate (mat g) := rfl
lemma spanningMatrix_0 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 0))) =
    spanningMatrix 0 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 0)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 0))⁻¹)) i = spanningMatrix 0 i j
  simp only [spanningWord_at_0, map_one, inv_one, mat_one, one_mul, mul_one,
    traceless_extract, spanningMatrix_at_0]
  fin_cases i <;> fin_cases j <;> norm_num [Pi.single_apply]

lemma spanningMatrix_1 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 1))) =
    spanningMatrix 1 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 1)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 1))⁻¹)) i = spanningMatrix 1 i j
  simp only [spanningWord_at_1, referenceRho_of, reference_mat_inv, reference_mat_0]
  fin_cases i <;> fin_cases j <;>
    norm_num [extract, traceless, Matrix.mul_apply,
      Matrix.adjugate_fin_two, Fin.sum_univ_two, Pi.single_apply, Fin.ext_iff]

lemma spanningMatrix_2 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 2))) =
    spanningMatrix 2 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 2)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 2))⁻¹)) i = spanningMatrix 2 i j
  simp only [spanningWord_at_2, map_mul, referenceRho_of,
    reference_mat_inv, mat_mul, reference_mat_0]
  fin_cases i <;> fin_cases j <;>
    norm_num [extract, traceless, Matrix.mul_apply,
      Matrix.adjugate_fin_two, Fin.sum_univ_two, Pi.single_apply, Fin.ext_iff]

lemma spanningMatrix_3 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 3))) =
    spanningMatrix 3 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 3)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 3))⁻¹)) i = spanningMatrix 3 i j
  simp only [spanningWord_at_3, referenceRho_of, reference_mat_inv, reference_mat_1]
  fin_cases i <;> fin_cases j <;>
    norm_num [extract, traceless, Matrix.mul_apply,
      Matrix.adjugate_fin_two, Fin.sum_univ_two, Pi.single_apply, Fin.ext_iff]

lemma spanningMatrix_4 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 4))) =
    spanningMatrix 4 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 4)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 4))⁻¹)) i = spanningMatrix 4 i j
  simp only [spanningWord_at_4, referenceRho_of, reference_mat_inv, reference_mat_2]
  fin_cases i <;> fin_cases j <;>
    norm_num [extract, traceless, Matrix.mul_apply,
      Matrix.adjugate_fin_two, Fin.sum_univ_two, Pi.single_apply, Fin.ext_iff]

lemma spanningMatrix_5 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 5))) =
    spanningMatrix 5 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 5)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 5))⁻¹)) i = spanningMatrix 5 i j
  simp only [spanningWord_at_5, map_mul, referenceRho_of,
    reference_mat_inv, mat_mul, reference_mat_0, reference_mat_1]
  fin_cases i <;> fin_cases j <;>
    norm_num [extract, traceless, Matrix.mul_apply,
      Matrix.adjugate_fin_two, Fin.sum_univ_two, Pi.single_apply, Fin.ext_iff]

lemma spanningMatrix_6 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 6))) =
    spanningMatrix 6 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 6)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 6))⁻¹)) i = spanningMatrix 6 i j
  simp only [spanningWord_at_6, map_mul, referenceRho_of,
    reference_mat_inv, mat_mul, reference_mat_0, reference_mat_2]
  fin_cases i <;> fin_cases j <;>
    norm_num [extract, traceless, Matrix.mul_apply,
      Matrix.adjugate_fin_two, Fin.sum_univ_two, Pi.single_apply, Fin.ext_iff]

lemma spanningMatrix_7 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 7))) =
    spanningMatrix 7 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 7)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 7))⁻¹)) i = spanningMatrix 7 i j
  simp only [spanningWord_at_7, map_mul, referenceRho_of,
    reference_mat_inv, mat_mul, reference_mat_0, reference_mat_1]
  fin_cases i <;> fin_cases j <;>
    norm_num [extract, traceless, Matrix.mul_apply,
      Matrix.adjugate_fin_two, Fin.sum_univ_two, Pi.single_apply, Fin.ext_iff]

lemma spanningMatrix_8 : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord 8))) =
    spanningMatrix 8 := by
  ext i j
  change extract (mat (referenceRho (spanningWord 8)) * traceless (Pi.single j 1) *
    mat ((referenceRho (spanningWord 8))⁻¹)) i = spanningMatrix 8 i j
  simp only [spanningWord_at_8, map_mul, referenceRho_of,
    reference_mat_inv, mat_mul, reference_mat_0, reference_mat_2]
  fin_cases i <;> fin_cases j <;>
    norm_num [extract, traceless, Matrix.mul_apply,
      Matrix.adjugate_fin_two, Fin.sum_univ_two, Pi.single_apply, Fin.ext_iff]

lemma spanningMatrix_eq (i : Fin 9) : LinearMap.toMatrix' (adjoint (referenceRho (spanningWord i))) =
    spanningMatrix i := by
  fin_cases i
  · exact spanningMatrix_0
  · exact spanningMatrix_1
  · exact spanningMatrix_2
  · exact spanningMatrix_3
  · exact spanningMatrix_4
  · exact spanningMatrix_5
  · exact spanningMatrix_6
  · exact spanningMatrix_7
  · exact spanningMatrix_8

lemma matrixUnit_00 : Matrix.single 0 0 (1:ℚ) =
    ((1/45) : ℚ) • spanningMatrix 0 +
    ((-1/9) : ℚ) • spanningMatrix 1 +
    ((4/45) : ℚ) • spanningMatrix 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

lemma matrixUnit_01 : Matrix.single 0 1 (1:ℚ) =
    ((-1/6) : ℚ) • spanningMatrix 0 +
    ((2/3) : ℚ) • spanningMatrix 1 +
    ((1/6) : ℚ) • spanningMatrix 3 +
    ((-2/3) : ℚ) • spanningMatrix 5 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

lemma matrixUnit_02 : Matrix.single 0 2 (1:ℚ) =
    (-1 : ℚ) • spanningMatrix 1 +
    ((4/3) : ℚ) • spanningMatrix 5 +
    ((-1/3) : ℚ) • spanningMatrix 7 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

lemma matrixUnit_10 : Matrix.single 1 0 (1:ℚ) =
    ((-1/3) : ℚ) • spanningMatrix 0 +
    ((4/3) : ℚ) • spanningMatrix 1 +
    ((1/3) : ℚ) • spanningMatrix 4 +
    ((-4/3) : ℚ) • spanningMatrix 8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

lemma matrixUnit_11 : Matrix.single 1 1 (1:ℚ) =
    ((-4/9) : ℚ) • spanningMatrix 0 +
    ((17/9) : ℚ) • spanningMatrix 1 +
    ((-4/9) : ℚ) • spanningMatrix 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

lemma matrixUnit_12 : Matrix.single 1 2 (1:ℚ) =
    ((-4/3) : ℚ) • spanningMatrix 0 +
    ((1/3) : ℚ) • spanningMatrix 1 +
    ((4/3) : ℚ) • spanningMatrix 3 +
    ((-1/3) : ℚ) • spanningMatrix 7 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

lemma matrixUnit_20 : Matrix.single 2 0 (1:ℚ) =
    (-1 : ℚ) • spanningMatrix 1 +
    ((-1/3) : ℚ) • spanningMatrix 6 +
    ((4/3) : ℚ) • spanningMatrix 8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

lemma matrixUnit_21 : Matrix.single 2 1 (1:ℚ) =
    ((-2/3) : ℚ) • spanningMatrix 0 +
    ((1/6) : ℚ) • spanningMatrix 1 +
    ((2/3) : ℚ) • spanningMatrix 4 +
    ((-1/6) : ℚ) • spanningMatrix 6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

lemma matrixUnit_22 : Matrix.single 2 2 (1:ℚ) =
    ((64/45) : ℚ) • spanningMatrix 0 +
    ((-16/9) : ℚ) • spanningMatrix 1 +
    ((16/45) : ℚ) • spanningMatrix 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply]

 

lemma shortWords_finite : shortWords.Finite := by
  let f : (Σ n : Fin 6, Fin n.val → Fin 3 × Bool) → shortWords := fun w ↦
    ⟨FreeGroup.mk (List.ofFn w.2),
      FreeGroup.norm_mk_le.trans (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g,hg⟩
    refine ⟨⟨⟨FreeGroup.norm g, Nat.lt_succ_of_le hg⟩,g.toWord.get⟩, ?_⟩
    apply Subtype.ext
    change FreeGroup.mk (List.ofFn g.toWord.get) = g
    simpa only [List.ofFn_get] using (FreeGroup.mk_toWord (x := g))
  let : Finite shortWords := Finite.of_surjective f hf
  exact Set.toFinite _

lemma one_mem_shortWords : (1 : FreeGroup (Fin 3)) ∈ shortWords := by
  simp [shortWords]

lemma inv_mem_shortWords {g : FreeGroup (Fin 3)} (hg : g ∈ shortWords) :
    g⁻¹ ∈ shortWords := by simpa only [shortWords, Set.mem_ofPred_eq, FreeGroup.norm_inv_eq] using hg

 

def reverseWord (g : FreeGroup (Fin 3)) : FreeGroup (Fin 3) :=
  FreeGroup.mk g.toWord.reverse

lemma reverse_mem_shortWords {g : FreeGroup (Fin 3)} (hg : g ∈ shortWords) :
    reverseWord g ∈ shortWords := by
  change FreeGroup.norm (FreeGroup.mk g.toWord.reverse) ≤ 5
  change g.toWord.length ≤ 5 at hg
  apply FreeGroup.norm_mk_le.trans
  simpa only [List.length_reverse] using hg

lemma reference_matrix_span : Submodule.span ℚ
    (Set.range (fun c : shortWords ↦ LinearMap.toMatrix' (adjoint (referenceRho c)))) = ⊤ := by
  let S := Submodule.span ℚ
    (Set.range (fun c : shortWords ↦ LinearMap.toMatrix' (adjoint (referenceRho c))))
  have hm (i : Fin 9) : spanningMatrix i ∈ S := by
    rw [← spanningMatrix_eq]
    exact Submodule.subset_span ⟨⟨spanningWord i,spanningWord_mem i⟩,rfl⟩
  have hs (i j : Fin 3) : Matrix.single i j (1:ℚ) ∈ S := by
    fin_cases i <;> fin_cases j
    · change Matrix.single 0 0 (1:ℚ) ∈ S
      rw [matrixUnit_00]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
    · change Matrix.single 0 1 (1:ℚ) ∈ S
      rw [matrixUnit_01]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
    · change Matrix.single 0 2 (1:ℚ) ∈ S
      rw [matrixUnit_02]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
    · change Matrix.single 1 0 (1:ℚ) ∈ S
      rw [matrixUnit_10]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
    · change Matrix.single 1 1 (1:ℚ) ∈ S
      rw [matrixUnit_11]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
    · change Matrix.single 1 2 (1:ℚ) ∈ S
      rw [matrixUnit_12]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
    · change Matrix.single 2 0 (1:ℚ) ∈ S
      rw [matrixUnit_20]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
    · change Matrix.single 2 1 (1:ℚ) ∈ S
      rw [matrixUnit_21]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
    · change Matrix.single 2 2 (1:ℚ) ∈ S
      rw [matrixUnit_22]
      repeat' first | exact hm _ | apply S.add_mem | apply S.smul_mem
  apply top_unique
  intro B _
  rw [Matrix.matrix_eq_sum_single B]
  apply S.sum_mem; intro i _
  apply S.sum_mem; intro j _
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using S.smul_mem (B i j) (hs i j)

theorem finite_reference_adjoint_span : Submodule.span ℚ
    (Set.range (fun c : shortWords ↦ adjoint (referenceRho c))) = ⊤ := by
  have h := congrArg (Submodule.map Matrix.toLin'.toLinearMap) reference_matrix_span
  simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearEquiv.range, Function.comp_def, LinearEquiv.coe_coe,
    Matrix.toLin'_toMatrix'] using h

end BoundaryOnly.Holonomy
end

end OAI
