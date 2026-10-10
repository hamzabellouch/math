import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Matrix.Trace
import OAI.Probability.SKGap.Stability.OrdinaryGraph
import OAI.Probability.SKGap.Matrix.CorrectionTrace
import OAI.Probability.SKGap.Localization.RecipeGraph

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype κ] in
lemma sourceError_rearrange (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>coefficient H θ F x i*s x i) x=
      Matrix.diagonal (coefficient H θ F x)*derivativeMatrix s x+
      (∑l,Matrix.diagonal (fun i=>s x i*localPartial H θ F' (.inl l) x i)*derivativeMatrix (H l) x)+
      sourceError H θ F F' s x := by unfold sourceError; abel

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

def sourceAtoms (a : ℕ) (Y : Fin a→VectorFields n) (x : Spin n) : Interaction n :=
  (∑s,sourceError D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) (fun _=>D.seed s) x)+
  ∑b,sourceError D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) (Y b) x

lemma sourceOf_derivative (a : ℕ) (Y : Fin a→VectorFields n) (x : Spin n) :
    derivativeMatrix (D.sourceOf a Y) x=
      (∑b,Matrix.diagonal (D.auxCoefficient a b x)*derivativeMatrix (Y b) x)+
      (∑l,Matrix.diagonal (D.partialOf a l Y x)*derivativeMatrix (D.H l) x)+D.sourceAtoms a Y x := by
  have he : D.sourceOf a Y=(fun x i=>(∑s,D.seedCoefficient a s x i*D.seed s i)+
      (∑b,D.auxCoefficient a b x i*Y b x i)) := rfl
  rw [he,derivativeMatrix_add,derivativeMatrix_sum,derivativeMatrix_sum]
  have hs (s : σ) := sourceError_rearrange D.H D.θ (D.seedFunction a s)
    (D.seedDerivative a s) (fun _=>D.seed s) x
  have hb (b : Fin a) := sourceError_rearrange D.H D.θ (D.auxFunction a b)
    (D.auxDerivative a b) (Y b) x
  change (∑s,derivativeMatrix (fun x i=>coefficient D.H D.θ (D.seedFunction a s) x i*D.seed s i) x)+
    (∑b,derivativeMatrix (fun x i=>coefficient D.H D.θ (D.auxFunction a b) x i*Y b x i) x)=_
  simp_rw [hs,hb]
  simp only [Finset.sum_add_distrib]
  have hz (s : σ) : derivativeMatrix (fun _ : Spin n=>D.seed s) x=0 := by
    ext i k; simp [derivativeMatrix,halfDiff]
  simp only [hz,mul_zero,Finset.sum_const_zero,zero_add]
  have hparts :
      (∑s,∑l,Matrix.diagonal (fun i=>D.seed s i*localPartial D.H D.θ (D.seedDerivative a s) (.inl l) x i)*derivativeMatrix (D.H l) x)+
      (∑b,∑l,Matrix.diagonal (fun i=>Y b x i*localPartial D.H D.θ (D.auxDerivative a b) (.inl l) x i)*derivativeMatrix (D.H l) x)=
      ∑l,Matrix.diagonal (D.partialOf a l Y x)*derivativeMatrix (D.H l) x := by
    rw [Finset.sum_comm (f:=fun s l=>Matrix.diagonal (fun i=>D.seed s i*localPartial D.H D.θ (D.seedDerivative a s) (.inl l) x i)*derivativeMatrix (D.H l) x),
      Finset.sum_comm (f:=fun b l=>Matrix.diagonal (fun i=>Y b x i*localPartial D.H D.θ (D.auxDerivative a b) (.inl l) x i)*derivativeMatrix (D.H l) x),
      ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _
    ext i k
    simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.diagonal_mul,partialOf,seedPartial,auxPartial,
      add_mul,Finset.sum_mul]
    congr 1 <;> (apply Finset.sum_congr rfl; intro b _; ring)
  dsimp only [sourceAtoms]
  rw [←hparts]
  simp only [auxCoefficient]
  abel

def sourceDerivativeError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  derivativeMatrix (D.source a) x-D.retainedSource T x a

def fieldDerivativeError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  derivativeMatrix (D.auxiliary a) x-D.retainedField T x a

lemma source_error_recursion (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.sourceDerivativeError T x a=
      (∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.fieldDerivativeError T x b)+
      (∑l,Matrix.diagonal (D.sourcePartial a l x)*
        (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)))+
      D.sourceAtoms a (fun b=>D.auxiliary b) x := by
  rw [sourceDerivativeError,D.source_eq,D.sourceOf_derivative,D.retainedSource_eq]
  simp only [fieldDerivativeError,mul_sub,Finset.sum_sub_distrib,sourcePartial]
  abel

lemma fieldOf_derivative (a : ℕ) (W Y : Fin a→VectorFields n) (x : Spin n) :
    derivativeMatrix (D.fieldOf a W Y) x=
      D.J*derivativeMatrix (D.sourceOf a Y) x-
      (∑l,(D.j*siteMean (D.partialOf a l Y) x) • derivativeMatrix (D.predecessor l) x)-
      (∑b,(D.j*siteMean (D.auxCoefficient a b) x) • derivativeMatrix (W b) x)-
      D.j • ((∑l,averageError (siteMean (D.partialOf a l Y)) (D.predecessor l) x)+
        ∑b,averageError (siteMean (D.auxCoefficient a b)) (W b) x) := by
  have he : D.fieldOf a W Y=(fun x i=>(0+D.J.mulVec (D.sourceOf a Y x) i)-
      (D.j*(∑l,siteMean (D.partialOf a l Y) x*D.predecessor l x i))-
      (D.j*(∑b,siteMean (D.auxCoefficient a b) x*W b x i))) := by
    ext x i; simp [fieldOf]
  rw [he,derivativeMatrix_sub,derivativeMatrix_sub]
  simp only [Matrix.mulVec, dotProduct]
  rw [derivativeMatrix_linear,
    derivativeMatrix_smul,derivativeMatrix_smul,derivativeMatrix_sum,derivativeMatrix_sum]
  have he₁ (l : ι) : derivativeMatrix (fun y i=>siteMean (D.partialOf a l Y) y*D.predecessor l y i) x=
      siteMean (D.partialOf a l Y) x • derivativeMatrix (D.predecessor l) x+
        averageError (siteMean (D.partialOf a l Y)) (D.predecessor l) x := by unfold averageError; abel
  have he₂ (b : Fin a) : derivativeMatrix (fun y i=>siteMean (D.auxCoefficient a b) y*W b y i) x=
      siteMean (D.auxCoefficient a b) x • derivativeMatrix (W b) x+
        averageError (siteMean (D.auxCoefficient a b)) (W b) x := by unfold averageError; abel
  simp only [he₁,he₂,Finset.sum_add_distrib,smul_add,Finset.smul_sum,smul_smul]
  abel

lemma field_error_recursion (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.fieldDerivativeError T x a=D.J*D.sourceDerivativeError T x a-
      (∑l,(D.j*siteMean (D.sourcePartial a l) x) •
        (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))-
      (∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.sourceDerivativeError T x b)-
      D.j • ((∑l,averageError (siteMean (D.sourcePartial a l)) (D.predecessor l) x)+
        ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.source b) x) := by
  rw [fieldDerivativeError,D.auxiliary_eq,D.fieldOf_derivative,D.retainedField_eq]
  rw [sourceDerivativeError,D.source_eq]
  simp only [sourceDerivativeError,smul_sub,Finset.sum_sub_distrib,mul_sub,sourcePartial]
  abel

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
