import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fixedSpace (p : H →L[ℂ] H) : Submodule ℂ H := (p-1).ker

omit [CompleteSpace H] in
@[simp] lemma mem_fixedSpace (p : H →L[ℂ] H) (x : H) : x∈fixedSpace p ↔ p x=x := by
  change p x-x=0 ↔ p x=x
  exact sub_eq_zero

instance (p : H →L[ℂ] H) : IsClosed ((fixedSpace p : Submodule ℂ H) : Set H) :=
  (p-1).isClosed_ker

instance (p : H →L[ℂ] H) : CompleteSpace (fixedSpace p) :=
  (p-1).isClosed_ker.completeSpace_coe

omit [CompleteSpace H] in
lemma fixed_apply (p : H →L[ℂ] H) (x : fixedSpace p) : p x=x :=
  (mem_fixedSpace p x).mp x.property

def insert (p v : H →L[ℂ] H) (hv : star v*v=p) : fixedSpace p →ₗᵢ[ℂ] H where
  toLinearMap := v.toLinearMap.comp (fixedSpace p).subtype
  norm_map' x := by
    have he : ‖v x‖^2=‖(x:H)‖^2 := by
      rw [@norm_sq_eq_re_inner ℂ H _ _, @norm_sq_eq_re_inner ℂ H _ _,←adjoint_inner_right]
      have hx : v.adjoint (v x)=p x := congrArg (fun T : H →L[ℂ] H => T x) hv
      rw [hx,fixed_apply]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

@[simp] lemma insert_apply (p v : H →L[ℂ] H) (hv : star v*v=p) (x : fixedSpace p) :
    insert p v hv x=v x := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (p : H →L[ℂ] H) (v : ι → H →L[ℂ] H)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

def matrixInsert (i : ι) : fixedSpace p →ₗᵢ[ℂ] H :=
  insert p (v i) (by simpa using hcol i i)

include hinit in
omit [Fintype ι] [DecidableEq ι] in
lemma adjoint_mem_fixed (i : ι) (x : H) : (star (v i)) x∈fixedSpace p := by
  rw [mem_fixedSpace]
  exact congrArg (fun T : H →L[ℂ] H => T x) (hinit i)

include hcol in
omit [Fintype ι] in
lemma matrixInsert_orthogonal : OrthogonalFamily ℂ (fun _ : ι => fixedSpace p)
    (matrixInsert p v hcol) := by
  intro i j hij x y
  change inner ℂ (v i x) (v j y)=0
  rw [←adjoint_inner_right]
  have he : (v i).adjoint (v j y)=0 := by
    simpa only [ite_eq_right hij,zero_apply,mul_apply_eq_comp,star_eq_adjoint] using congrArg (fun T : H →L[ℂ] H => T y) (hcol i j)
  rw [he,inner_zero_right]

include hinit in
omit [Fintype ι] in
lemma matrixInsert_adjoint (i : ι) (x : H) :
    (((matrixInsert p v hcol i).toContinuousLinearMap.adjoint x : fixedSpace p) : H)=
      (star (v i)) x := by
  have he : (matrixInsert p v hcol i).toContinuousLinearMap.adjoint x=
      (⟨(star (v i)) x,adjoint_mem_fixed p v hinit i x⟩ : fixedSpace p) := by
    apply ext_inner_left ℂ
    intro y
    rw [adjoint_inner_right]
    change inner ℂ (v i (y:H)) x=inner ℂ (y:H) ((v i).adjoint x)
    rw [adjoint_inner_right]
  exact congrArg (fun y : fixedSpace p => (y:H)) he

include hinit htotal in
lemma matrixInsert_isHilbertSum : IsHilbertSum ℂ (fun _ : ι => fixedSpace p)
    (matrixInsert p v hcol) := by
  apply IsHilbertSum.mk (matrixInsert_orthogonal p v hcol)
  intro x _
  have hx : ∑ i, v i ((star (v i)) x)=x := by
    simpa only [sum_apply,mul_apply_eq_comp,one_apply_eq_self] using
      congrArg (fun T : H →L[ℂ] H => T x) htotal
  rw [←hx]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.le_topologicalClosure
  apply Submodule.mem_iSup_of_mem i
  exact ⟨⟨(star (v i)) x,adjoint_mem_fixed p v hinit i x⟩,rfl⟩

end Kadison.MatrixCornerHilbert

end

end
end

end OAI
