import Mathlib
import OAI.Analysis.Commutator.HilbertBiprod

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

abbrev left : Space H G →L[ℂ] Space H G := block 1 0

abbrev right : Space H G →L[ℂ] Space H G := block 0 1

lemma left_projection : IsStarProjection (left (H:=H) (G:=G)) := by
  constructor
  · change block 1 0*block 1 0=block 1 0
    rw [←block_mul,one_mul,zero_mul]
  · change star (block (1:H →L[ℂ] H) (0:G →L[ℂ] G))=block 1 0
    rw [←block_star,star_one,star_zero]

lemma right_projection : IsStarProjection (right (H:=H) (G:=G)) := by
  constructor
  · change block 0 1*block 0 1=block 0 1
    rw [←block_mul,one_mul,zero_mul]
  · change star (block (0:H →L[ℂ] H) (1:G →L[ℂ] G))=block 0 1
    rw [←block_star,star_one,star_zero]

omit [CompleteSpace H] [CompleteSpace G] in
lemma left_add_right : left (H:=H) (G:=G)+right=1 := by
  rw [left,right,←block_add]
  simp

omit [CompleteSpace H] [CompleteSpace G] in
lemma left_mul_right : left (H:=H) (G:=G)*right=0 := by
  rw [left,right,←block_mul]
  simp

omit [CompleteSpace H] [CompleteSpace G] in
lemma left_commutes (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block S T*left=left*block S T := by
  rw [left,←block_mul,←block_mul]
  simp

omit [CompleteSpace H] [CompleteSpace G] in
lemma right_commutes (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block S T*right=right*block S T := by
  rw [right,←block_mul,←block_mul]
  simp

lemma adjoint_inlL : (inlL (H:=H) (G:=G)).adjoint=WithLp.fstL 2 ℂ H G := by
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_left,inlL_apply,WithLp.prod_inner_apply,
    inner_zero_right,add_zero]
  rfl

lemma adjoint_inrL : (inrL (H:=H) (G:=G)).adjoint=WithLp.sndL 2 ℂ H G := by
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_left,inrL_apply,WithLp.prod_inner_apply,
    inner_zero_right,zero_add]
  rfl

lemma inl_adjoint : (inlL (H:=H) (G:=G)).comp inlL.adjoint=left := by
  rw [adjoint_inlL]
  apply ext
  intro x
  rfl

lemma inr_adjoint : (inrL (H:=H) (G:=G)).comp inrL.adjoint=right := by
  rw [adjoint_inrL]
  apply ext
  intro x
  rfl

omit [CompleteSpace H] [CompleteSpace G] in
lemma right_ne_zero [Nontrivial G] : right (H:=H) (G:=G)≠0 := by
  obtain ⟨x,hx⟩ := exists_ne (0:G)
  intro hz
  apply hx
  have he := congrArg (fun T : Space H G →L[ℂ] Space H G => (T (inr x)).ofLp.2) hz
  change x=0 at he
  exact he

end Kadison.HilbertBiprod

end

end
end

end OAI
