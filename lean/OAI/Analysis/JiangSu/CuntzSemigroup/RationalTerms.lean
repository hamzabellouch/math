import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerMaps

namespace OAI

noncomputable section


namespace RationalTerms
inductive Term (J : Type*) where
  | scalar : ℚ → Term J
  | gen : J → Term J
  | add : Term J → Term J → Term J
  | mul : Term J → Term J → Term J
  | adjoint : Term J → Term J
  deriving Encodable

variable {J : Type*} {A B : Type*} [Semiring A] [StarRing A] [Algebra ℚ A] [StarModule ℚ A]
  [Semiring B] [StarRing B] [Algebra ℚ B] [StarModule ℚ B]
 def Term.eval (v : J→A) : Term J→A
  | .scalar z => algebraMap ℚ A z
  | .gen j => v j
  | .add e f => e.eval v+f.eval v
  | .mul e f => e.eval v*f.eval v
  | .adjoint e => star (e.eval v)
omit [StarModule ℚ A] [StarModule ℚ B] in
lemma Term.map_eval (e : Term J) (v : J→A) (π : A →⋆ₐ[ℚ] B) :
    π (e.eval v)=e.eval (π∘v) := by
  induction e with
  | scalar z => exact π.commutes z
  | gen j => rfl
  | add e f he hf => simp only [Term.eval,map_add,he,hf]
  | mul e f he hf => simp only [Term.eval,map_mul,he,hf]
  | adjoint e he => simp only [Term.eval,map_star,he]

 def evalRange (v : J→A) : StarSubalgebra ℚ A where
  carrier := Set.range (Term.eval v)
  zero_mem' := ⟨.scalar 0,map_zero _⟩
  one_mem' := ⟨.scalar 1,map_one _⟩
  add_mem' := by rintro a b ⟨e,rfl⟩ ⟨f,rfl⟩; exact ⟨.add e f,rfl⟩
  mul_mem' := by rintro a b ⟨e,rfl⟩ ⟨f,rfl⟩; exact ⟨.mul e f,rfl⟩
  algebraMap_mem' z := ⟨.scalar z,rfl⟩
  star_mem' := by rintro a ⟨e,rfl⟩; exact ⟨.adjoint e,rfl⟩
lemma evalRange_eq_adjoin (v : J→A) : evalRange v=StarAlgebra.adjoin ℚ (Set.range v) := by
  apply le_antisymm
  · rintro a ⟨e,rfl⟩
    induction e with
    | scalar z => exact StarSubalgebra.algebraMap_mem _ z
    | gen j => exact StarAlgebra.subset_adjoin ℚ _ ⟨j,rfl⟩
    | add e f he hf => exact add_mem he hf
    | mul e f he hf => exact mul_mem he hf
    | adjoint e he => exact star_mem he
  · apply StarAlgebra.adjoin_le_iff.mpr
    rintro a ⟨j,rfl⟩
    exact ⟨.gen j,rfl⟩

end RationalTerms

namespace RationalTerms
local instance rationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
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
 def lift : evalRange v →⋆ₐ[ℚ] B where
  toFun := liftedValue v w
  map_zero' := by simpa only [Term.eval,map_zero] using liftedValue_eq v w h 0 (.scalar 0) (map_zero _)
  map_one' := by simpa only [Term.eval,map_one] using liftedValue_eq v w h 1 (.scalar 1) (map_one _)
  commutes' z := liftedValue_eq v w h (algebraMap ℚ (evalRange v) z) (.scalar z) rfl
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

end RationalTerms


namespace RationalTerms
open NormUltra NormUltra.QuotientAlgebra DirectComparison
open scoped ENNReal

local instance familyRationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
variable {J A : Type*} [CStarAlgebra A]
 def Term.boundedEval (v : J→lp (fun _ : ℕ=>A) ∞) : Term J→lp (fun _ : ℕ=>A) ∞
 | .scalar q => boundedDiagonal (algebraMap ℚ A q)
 | .gen j => v j
 | .add e f => e.boundedEval v+f.boundedEval v
 | .mul e f => e.boundedEval v*f.boundedEval v
 | .adjoint e => star (e.boundedEval v)
lemma Term.boundedEval_apply (e : Term J) (v : J→lp (fun _ : ℕ=>A) ∞) (k : ℕ) :
    e.boundedEval v k=e.eval (fun j=>v j k) := by
  induction e with
  | scalar q => rfl
  | gen j => rfl
  | add e f he hf => change e.boundedEval v k+f.boundedEval v k=_; rw [he,hf]; rfl
  | mul e f he hf => change e.boundedEval v k*f.boundedEval v k=_; rw [he,hf]; rfl
  | adjoint e he => change star (e.boundedEval v k)=_; rw [he]; rfl
lemma Term.mk_boundedEval (e : Term J) (v : J→lp (fun _ : ℕ=>A) ∞) (U : Ultrafilter ℕ) :
    mk U (e.boundedEval v)=e.eval (fun j=>mk U (v j)) := by
  induction e with
  | scalar q =>
    change diagonalHom U (algebraMap ℂ A (q:ℂ))=algebraMap ℂ _ (q:ℂ)
    exact (diagonalHom U).commutes _
  | gen j => rfl
   | add e f he hf => simp only [Term.boundedEval,Term.eval,mk_add,he,hf]
   | mul e f he hf => simp only [Term.boundedEval,Term.eval,mk_mul,he,hf]
   | adjoint e he => simp only [Term.boundedEval,Term.eval,mk_star,he]

 def Term.support [DecidableEq J] : Term J→Finset J
 | .scalar _ => ∅
 | .gen j => {j}
 | .add e f => e.support∪f.support
 | .mul e f => e.support∪f.support
 | .adjoint e => e.support
lemma Term.eval_agree [DecidableEq J] (e : Term J) (v w : J→A)
    (h : ∀ j∈e.support,v j=w j) : e.eval v=e.eval w := by
  induction e with
  | scalar q => rfl
  | gen j => exact h j (Finset.mem_singleton_self j)
  | add e f he hf =>
    exact congrArg₂ (·+·) (he (fun j hj=>h j (Finset.mem_union_left _ hj)))
      (hf (fun j hj=>h j (Finset.mem_union_right _ hj)))
  | mul e f he hf =>
    exact congrArg₂ (·*·) (he (fun j hj=>h j (Finset.mem_union_left _ hj)))
      (hf (fun j hj=>h j (Finset.mem_union_right _ hj)))
  | adjoint e he => exact congrArg star (he h)
end RationalTerms

end

end OAI
