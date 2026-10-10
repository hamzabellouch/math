import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.StarTerms
import OAI.Analysis.JiangSu.TensorProducts.StarHomClosureExtension

namespace OAI

section

noncomputable section
namespace StarTerms
variable {J A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
 def Term.sub (e f : Term J) : Term J := .add e (.mul (.scalar (-1)) f)
lemma Term.eval_sub (e f : Term J) (v : J→A) : (e.sub f).eval v=e.eval v-f.eval v := by
  simp [Term.sub,Term.eval,sub_eq_add_neg]
variable (v : J→A) (w : J→B) (h : ∀ e : Term J,‖e.eval w‖≤‖e.eval v‖)
include h
lemma eval_eq_of_norm (e f : Term J) (hef : e.eval v=f.eval v) : e.eval w=f.eval w := by
  have hn := h (e.sub f)
  rw [Term.eval_sub,Term.eval_sub,hef,sub_self,norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
 def liftedValue (x : evalRange v) : B := (Classical.choose x.property).eval w
lemma liftedValue_eq (x : evalRange v) (e : Term J) (he : e.eval v=x) : liftedValue v w x=e.eval w :=
  eval_eq_of_norm v w h _ e ((Classical.choose_spec x.property).trans he.symm)
 def lift : evalRange v →⋆ₐ[ℂ] B where
  toFun := liftedValue v w
  map_zero' := by simpa only [Term.eval,map_zero] using liftedValue_eq v w h 0 (.scalar 0) (map_zero _)
  map_one' := by simpa only [Term.eval,map_one] using liftedValue_eq v w h 1 (.scalar 1) (map_one _)
  commutes' z := liftedValue_eq v w h (algebraMap ℂ (evalRange v) z) (.scalar z) rfl
  map_add' x y := by
    obtain ⟨e,he⟩ := x.property
    obtain ⟨f,hf⟩ := y.property
    rw [liftedValue_eq v w h x e he,liftedValue_eq v w h y f hf]
    exact liftedValue_eq v w h (x+y) (.add e f) (by change e.eval v+f.eval v=(x:A)+(y:A); rw [he,hf])
  map_mul' x y := by
    obtain ⟨e,he⟩ := x.property
    obtain ⟨f,hf⟩ := y.property
    rw [liftedValue_eq v w h x e he,liftedValue_eq v w h y f hf]
    exact liftedValue_eq v w h (x*y) (.mul e f) (by change e.eval v*f.eval v=(x:A)*(y:A); rw [he,hf])
  map_star' x := by
    obtain ⟨e,he⟩ := x.property
    rw [liftedValue_eq v w h x e he]
    exact liftedValue_eq v w h (star x) (.adjoint e) (by change star (e.eval v)=star (x:A); rw [he])
lemma lift_norm (x : evalRange v) : ‖lift v w h x‖≤‖x‖ := by
  obtain ⟨e,he⟩ := x.property
  change ‖liftedValue v w x‖≤‖(x:A)‖
  rw [liftedValue_eq v w h x e he,←he]
  exact h e
 def closureLift : (evalRange v).topologicalClosure →⋆ₐ[ℂ] B :=
  StarHomClosure.extension _ (lift v w h) (lift_norm v w h)
lemma closureLift_eval (e : Term J) :
    closureLift v w h ⟨e.eval v,(evalRange v).le_topologicalClosure ⟨e,rfl⟩⟩=e.eval w := by
  change closureLift v w h (StarHomClosure.inclusion _ ⟨e.eval v,⟨e,rfl⟩⟩)=_
  rw [closureLift,StarHomClosure.extension_eq]
  exact liftedValue_eq v w h _ e rfl
lemma closureLift_gen (j : J) :
    closureLift v w h ⟨v j,(evalRange v).le_topologicalClosure ⟨.gen j,rfl⟩⟩=w j :=
  closureLift_eval v w h (.gen j)
end StarTerms

end
end

end OAI
