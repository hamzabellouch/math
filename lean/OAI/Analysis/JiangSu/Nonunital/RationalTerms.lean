import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.RationalTerms

namespace OAI

section

noncomputable section
namespace RationalTerms
open NormUltra NormUltra.QuotientAlgebra NonunitalGamma
open scoped ENNReal

variable {J A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def Term.localEval (u : A) (v : J→A) : Term J → A
  | .scalar q => (q:ℂ) • u
  | .gen j => v j
  | .add e f => e.localEval u v + f.localEval u v
  | .mul e f => e.localEval u v * f.localEval u v
  | .adjoint e => star (e.localEval u v)

lemma Term.map_localEval (e : Term J) (u : A) (v : J→A) (π : A →⋆ₙₐ[ℂ] B) :
    π (e.localEval u v)=e.localEval (π u) (π∘v) := by
  induction e with
  | scalar q => exact map_smul π (q:ℂ) u
  | gen j => rfl
  | add e f he hf => simp only [Term.localEval,map_add,he,hf]
  | mul e f he hf => simp only [Term.localEval,map_mul,he,hf]
  | adjoint e he => simp only [Term.localEval,map_star,he]

local instance localEvalRationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
lemma Term.localEval_one {D : Type*} [CStarAlgebra D] (e : Term J) (v : J→D) :
    e.localEval 1 v=e.eval v := by
  induction e with
  | scalar q => exact (Algebra.algebraMap_eq_smul_one (R := ℂ) (q:ℂ)).symm
  | gen j => rfl
  | add e f he hf => simp only [Term.localEval,Term.eval,he,hf]
  | mul e f he hf => simp only [Term.localEval,Term.eval,he,hf]
  | adjoint e he => simp only [Term.localEval,Term.eval,he]

lemma Term.localEval_apply (e : Term J) (u : lp (fun _ : ℕ=>A) ∞)
    (v : J→lp (fun _ : ℕ=>A) ∞) (k : ℕ) :
    e.localEval u v k=e.localEval (u k) (fun j=>v j k) := by
  induction e with
  | scalar q => rfl
  | gen j => rfl
  | add e f he hf => change e.localEval u v k+f.localEval u v k=_; rw [he,hf]; rfl
  | mul e f he hf => change e.localEval u v k*f.localEval u v k=_; rw [he,hf]; rfl
  | adjoint e he => change star (e.localEval u v k)=_; rw [he]; rfl

lemma Term.mk_localEval (e : Term J) (u : lp (fun _ : ℕ=>A) ∞)
    (v : J→lp (fun _ : ℕ=>A) ∞) (U : Ultrafilter ℕ) :
    mk U (e.localEval u v)=e.localEval (mk U u) (fun j=>mk U (v j)) :=
  e.map_localEval u v (mkHom (U := U))

end RationalTerms

end
end

end OAI
