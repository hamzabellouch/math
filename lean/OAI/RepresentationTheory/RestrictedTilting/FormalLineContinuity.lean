import OAI.RepresentationTheory.RestrictedTilting.FormalLine
import OAI.RepresentationTheory.RestrictedTilting.ClearedPolynomial

namespace OAI

namespace FiberFunctorProof
universe u
variable (k : Type u) [Field k]
local notation "A" => MvPolynomial (Fin 2) k
local notation "I" => MvPolynomial.idealOfVars (Fin 2) k

lemma formalLineMap_of_linePolynomial (P : A) :
    formalLineMap k (AdicCompletion.of I A P) =
      Polynomial.aeval (PowerSeries.X : PowerSeries k) (linePolynomial k P) := by
  change formalLineMap k (algebraMap A (planeCompletion k) P) = _
  rw [formalLineMap_of]
  have he : (Polynomial.aeval (PowerSeries.X : PowerSeries k)).comp (linePolynomial k) =
      MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then PowerSeries.X else 0) := by
    ext i
    simp only [AlgHom.comp_apply, linePolynomial, MvPolynomial.aeval_X]
    split_ifs <;> simp
  exact congrArg (fun f : A →ₐ[k] PowerSeries k => f P) he.symm

variable {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]

 

lemma formalLine_map_eq_of_representatives
    (F G : M →ₗ[A] A) (x y : AdicCompletion I M)
    (h : ∀ n : ℕ, ∃ v w : M,
      x.val (n+1) = (AdicCompletion.of I M v).val (n+1) ∧
      y.val (n+1) = (AdicCompletion.of I M w).val (n+1) ∧
      linePolynomial k (F v) = linePolynomial k (G w)) :
    formalLineMap k (AdicCompletion.map I F x) =
      formalLineMap k (AdicCompletion.map I G y) := by
  ext n
  obtain ⟨v,w,hv,hw,he⟩ := h n
  have hF : (AdicCompletion.map I F x).val (n+1) =
      (AdicCompletion.of I A (F v)).val (n+1) := by
    rw [← AdicCompletion.map_of]
    simp only [AdicCompletion.map_val_apply, hv]
  have hG : (AdicCompletion.map I G y).val (n+1) =
      (AdicCompletion.of I A (G w)).val (n+1) := by
    rw [← AdicCompletion.map_of]
    simp only [AdicCompletion.map_val_apply, hw]
  rw [formalLineMap_coeff_eq k n _ _ hF, formalLineMap_coeff_eq k n _ _ hG,
    formalLineMap_of_linePolynomial, formalLineMap_of_linePolynomial, he]
end FiberFunctorProof

end OAI
