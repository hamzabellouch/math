import Mathlib

namespace OAI

noncomputable section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMap

namespace Kadison.HilbertSum

variable {ι : Type*} [DecidableEq ι] (E : ι → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]

abbrev space := lp E 2

def insert (i : ι) : E i →L[ℂ] space E := lp.singleContinuousLinearMap ℂ E 2 i

def project (i : ι) : space E →L[ℂ] E i := lp.evalCLM ℂ E 2 i

omit [∀ i, CompleteSpace (E i)] in
@[simp] lemma insert_apply (i : ι) (x : E i) : insert E i x = lp.single 2 i x := rfl

omit [DecidableEq ι] [∀ i, CompleteSpace (E i)] in
@[simp] lemma project_apply (i : ι) (x : space E) : project E i x = x i := rfl

omit [∀ i, CompleteSpace (E i)] in
@[simp] lemma inner_insert (i : ι) (x : E i) (y : space E) :
    inner ℂ (insert E i x) y = inner ℂ x (project E i y) := lp.inner_single_left _ _ _

@[simp] lemma adjoint_insert (i : ι) : (insert E i).adjoint = project E i := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [adjoint_inner_right, inner_insert]

@[simp] lemma adjoint_project (i : ι) : (project E i).adjoint = insert E i := by
  rw [← adjoint_insert, adjoint_adjoint]

omit [∀ i, CompleteSpace (E i)] in
@[simp] lemma norm_insert_apply (i : ι) (x : E i) : ‖insert E i x‖ = ‖x‖ :=
  lp.norm_single (by norm_num) _ _

omit [DecidableEq ι] [∀ i, CompleteSpace (E i)] in
lemma norm_project_apply_le (i : ι) (x : space E) : ‖project E i x‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by norm_num) x i

omit [∀ i, CompleteSpace (E i)] in
@[simp] lemma project_insert (i : ι) : (project E i).comp (insert E i) = 1 := by
  ext x
  simp only [comp_apply, project_apply, insert_apply, lp.single_apply, Pi.single_eq_same,
    one_apply_eq_self]

omit [∀ i, CompleteSpace (E i)] in
lemma project_insert_ne {i j : ι} (h : i ≠ j) : (project E i).comp (insert E j) = 0 := by
  ext x
  simp only [comp_apply, project_apply, insert_apply, lp.single_apply, Pi.single_eq_of_ne h,
    zero_apply]

def block (T : space E →L[ℂ] space E) (i j : ι) : E j →L[ℂ] E i :=
  ((project E i).comp T).comp (insert E j)

omit [∀ i, CompleteSpace (E i)] in
@[simp] lemma block_apply (T : space E →L[ℂ] space E) (i j : ι) (x : E j) :
    block E T i j x = (T (insert E j x)) i := rfl

lemma norm_block_le (T : space E →L[ℂ] space E) (i j : ι) : ‖block E T i j‖ ≤ ‖T‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (norm_project_apply_le E i (T (insert E j x))).trans
    ((le_opNorm T (insert E j x)).trans_eq (by rw [norm_insert_apply]))

@[simp] lemma block_adjoint (T : space E →L[ℂ] space E) (i j : ι) :
    block E T.adjoint i j = (block E T j i).adjoint := by
  simp only [block, adjoint_comp, adjoint_project, adjoint_insert, comp_assoc]

omit [∀ i, CompleteSpace (E i)] in
lemma reduces_of_offdiagonal (T : space E →L[ℂ] space E)
    (h : ∀ i j, i ≠ j → block E T i j = 0) (j : ι) :
    T.comp (insert E j) = (insert E j).comp (block E T j j) := by
  ext x i
  by_cases hij : i = j
  · subst i
    simp only [comp_apply, insert_apply, lp.single_apply, Pi.single_eq_same, block_apply]
  · have ht := congrArg (fun R : E j →L[ℂ] E i => R x) (h i j hij)
    simpa only [block_apply, zero_apply, comp_apply, insert_apply, lp.single_apply,
      Pi.single_eq_of_ne hij] using ht

lemma adjoint_reduces_of_offdiagonal (T : space E →L[ℂ] space E)
    (h : ∀ i j, i ≠ j → block E T i j = 0) (j : ι) :
    T.adjoint.comp (insert E j) = (insert E j).comp (block E T j j).adjoint := by
  rw [← block_adjoint]
  apply reduces_of_offdiagonal
  intro i k hik
  rw [block_adjoint, h k i hik.symm, map_zero]

omit [∀ i, CompleteSpace (E i)] in
lemma block_covariant (T L R : space E →L[ℂ] space E)
    (l r : ∀ i, E i →L[ℂ] E i)
    (h : T.comp L = R.comp T)
    (hL : ∀ j, L.comp (insert E j) = (insert E j).comp (l j))
    (hR : ∀ i, (project E i).comp R = (r i).comp (project E i))
    (i j : ι) : (block E T i j).comp (l j) = (r i).comp (block E T i j) := by
  simp only [block, comp_assoc]
  rw [← hL, ← comp_assoc T, h, comp_assoc R, ← comp_assoc (project E i), hR, comp_assoc]

lemma project_covariant_of_adjoint (L : space E →L[ℂ] space E)
    (l : ∀ i, E i →L[ℂ] E i)
    (h : ∀ i, L.adjoint.comp (insert E i) = (insert E i).comp (l i).adjoint) (i : ι) :
    (project E i).comp L = (l i).comp (project E i) := by
  have hi := congrArg (ContinuousLinearMap.adjoint) (h i)
  simpa only [adjoint_comp, adjoint_insert, adjoint_adjoint] using hi

end Kadison.HilbertSum
end
end

end OAI
