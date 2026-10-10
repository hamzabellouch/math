import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap

namespace Kadison.ActualHilbertSum

variable {ι H : Type*} (E : ι → Type*)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]

variable (U : ∀ i, E i →ₗᵢ[ℂ] H)

abbrev insert (i : ι) := (U i).toContinuousLinearMap

def project (i : ι) : H →L[ℂ] E i := (insert E U i).adjoint

def block (T : H →L[ℂ] H) (i j : ι) : E j →L[ℂ] E i :=
  ((project E U i).comp T).comp (insert E U j)

@[simp] lemma project_insert (i : ι) : (project E U i).comp (insert E U i) = 1 := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [comp_apply, project, adjoint_inner_right, insert,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.inner_map_map,
    one_apply_eq_self]

lemma norm_project_le (i : ι) : ‖project E U i‖ ≤ 1 := by
  rw [project, adjoint.norm_map]
  exact (U i).norm_toContinuousLinearMap_le

lemma norm_block_le (T : H →L[ℂ] H) (i j : ι) : ‖block E U T i j‖ ≤ ‖T‖ := by
  calc
    ‖block E U T i j‖ ≤ (‖project E U i‖ * ‖T‖) * ‖insert E U j‖ :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
        (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (norm_project_le E U i) (norm_nonneg T))
      (U j).norm_toContinuousLinearMap_le (norm_nonneg _)
      (by simp)
    _ = ‖T‖ := by ring

@[simp] lemma block_adjoint (T : H →L[ℂ] H) (i j : ι) :
    block E U T.adjoint i j = (block E U T j i).adjoint := by
  simp only [block, project, adjoint_comp, adjoint_adjoint, comp_assoc]

variable (hU : IsHilbertSum ℂ E U)

lemma project_coordinates (i : ι) (x : H) :
    project E U i x = hU.linearIsometryEquiv x i := by
  classical
  apply ext_inner_left ℂ
  intro y
  rw [project, adjoint_inner_right]
  change inner ℂ (U i y) x = _
  rw [← hU.linearIsometryEquiv_symm_apply_single y]
  have := hU.linearIsometryEquiv.symm.inner_map_map
    (lp.single 2 i y) (hU.linearIsometryEquiv x)
  simpa only [LinearIsometryEquiv.symm_apply_apply, lp.inner_single_left] using this

include hU in
lemma ext_vectors {x y : H} (h : ∀ i, project E U i x=project E U i y) : x=y := by
  apply hU.linearIsometryEquiv.injective
  ext i
  simpa only [project_coordinates E U hU] using h i

include hU in
lemma project_insert_ne {i j : ι} (hij : i≠j) :
    (project E U i).comp (insert E U j) = 0 := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [comp_apply, project, adjoint_inner_right, insert,
    LinearIsometry.coe_toContinuousLinearMap, zero_apply, inner_zero_right]
  exact hU.OrthogonalFamily hij y x

include hU in
lemma reduces_of_offdiagonal (T : H →L[ℂ] H)
    (h : ∀ i j, i≠j → block E U T i j=0) (j : ι) :
    T.comp (insert E U j)=(insert E U j).comp (block E U T j j) := by
  ext x
  apply ext_vectors E U hU
  intro i
  by_cases hij : i=j
  · subst i
    change block E U T j j x = ((project E U j).comp (insert E U j)) _
    rw [project_insert,one_apply_eq_self]
    rfl
  · change block E U T i j x = ((project E U i).comp (insert E U j)) _
    rw [h i j hij,project_insert_ne E U hU hij]
    rfl

include hU in
lemma adjoint_reduces_of_offdiagonal (T : H →L[ℂ] H)
    (h : ∀ i j, i≠j → block E U T i j=0) (j : ι) :
    T.adjoint.comp (insert E U j)=(insert E U j).comp (block E U T j j).adjoint := by
  rw [←block_adjoint]
  apply reduces_of_offdiagonal E U hU
  intro i k hik
  rw [block_adjoint,h k i hik.symm,map_zero]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [∀ i, CompleteSpace (E i)] in
include hU in
lemma map_ext (T R : H →L[ℂ] F)
    (h : ∀ i, T.comp (insert E U i)=R.comp (insert E U i)) : T=R := by
  classical
  have he : T.comp hU.linearIsometryEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      R.comp hU.linearIsometryEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro i
    ext x
    have hi := congrArg (fun K : E i →L[ℂ] F => K x) (h i)
    change T (hU.linearIsometryEquiv.symm (lp.single 2 i x)) =
      R (hU.linearIsometryEquiv.symm (lp.single 2 i x))
    rw [hU.linearIsometryEquiv_symm_apply_single]
    exact hi
  ext x
  have hx := congrArg (fun K : lp E 2 →L[ℂ] F => K (hU.linearIsometryEquiv x)) he
  simpa only [comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] using hx

include hU in
lemma project_covariant (L : H →L[ℂ] H) (l : ∀ i, E i →L[ℂ] E i)
    (h : ∀ i, L.comp (insert E U i)=(insert E U i).comp (l i)) (i : ι) :
    (project E U i).comp L=(l i).comp (project E U i) := by
  apply map_ext E U hU
  intro j
  rw [comp_assoc, h j, ←comp_assoc, comp_assoc (l i)]
  by_cases hij : i=j
  · subst i
    rw [project_insert]
    ext x
    rfl
  · rw [project_insert_ne E U hU hij]
    simp

omit hU in
lemma block_covariant (T L R : H →L[ℂ] H) (l r : ∀ i, E i →L[ℂ] E i)
    (h : T.comp L=R.comp T)
    (hL : ∀ j, L.comp (insert E U j)=(insert E U j).comp (l j))
    (hR : ∀ i, (project E U i).comp R=(r i).comp (project E U i))
    (i j : ι) : (block E U T i j).comp (l j)=(r i).comp (block E U T i j) := by
  simp only [block,comp_assoc]
  rw [←hL,←comp_assoc T,h,comp_assoc R,←comp_assoc (project E U i),hR,comp_assoc]

include hU in
lemma block_covariant_of_insert (T L : H →L[ℂ] H) (l : ∀ i, E i →L[ℂ] E i)
    (h : T.comp L=L.comp T)
    (hL : ∀ j, L.comp (insert E U j)=(insert E U j).comp (l j)) (i j : ι) :
    (block E U T i j).comp (l j)=(l i).comp (block E U T i j) :=
  block_covariant E U T L L l l h hL (project_covariant E U hU L l hL) i j

omit hU in
lemma project_covariant_of_adjoint (L : H →L[ℂ] H) (l : ∀ i, E i →L[ℂ] E i)
    (h : ∀ i, L.adjoint.comp (insert E U i)=(insert E U i).comp (l i).adjoint) (i : ι) :
    (project E U i).comp L=(l i).comp (project E U i) := by
  have hi := congrArg ContinuousLinearMap.adjoint (h i)
  simpa only [adjoint_comp,adjoint_adjoint,project] using hi

end Kadison.ActualHilbertSum
end

end OAI
