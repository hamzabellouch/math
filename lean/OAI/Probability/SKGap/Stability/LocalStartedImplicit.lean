import Mathlib
import OAI.Probability.SKGap.Matrix.ClosedErrorTrace
import OAI.Probability.SKGap.Localization.StartedGraph
import OAI.Probability.SKGap.Stability.LocalImplicitNode
import OAI.Probability.SKGap.Stability.ImplicitTraceControl
import OAI.Probability.SKGap.Matrix.StartedNodeTrace

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ κ₀ σ₀ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable (D : OrdinaryData n ι κ σ) (I : OrdinaryData n Unit κ₀ σ₀)
variable (w y : VectorFields n) (T : ι→SourceTree (Fin n→ℝ)) (t : SourceTree (Fin n→ℝ))

lemma started_implicit_initial_errors_local (hj : D.j=I.j) (hJ : D.J=I.J)
    (x : Spin n)
    (hW : w x=I.sourceOf 1 (fun _=>y) x)
    (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
    (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i))
    (ha : ∀i,0≤I.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
      (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef) :
    let t₀:=ClosedTree.implicit (I.implicitPartial y x) t
    let a₀:=I.implicitCoefficient x
    D.startedSourceError w y T t₀ a₀ x 0=
      WordLetter.inverse.exactEval D.j a₀ D.J*
        (I.implicitSourcePrimitive t y x+Matrix.diagonal a₀*I.implicitFieldPrimitive t w y x) ∧
    D.startedFieldError w y T t₀ a₀ x 0=
      (D.J-(I.j*siteMean I.implicitCoefficient x) • 1)*D.startedSourceError w y T t₀ a₀ x 0+
        I.implicitFieldPrimitive t w y x := by
  have H:=I.implicit_error_solved_local t w y x hW hWf hY hYf (I.implicit_inverse_left x ha hS)
  dsimp only
  simp only [startedSourceError_zero,startedFieldError_zero,hj,hJ,ClosedTree.sourceMatrix,
    ClosedTree.fieldMatrix,ClosedTree.words]
  exact H

theorem implicit_started_error_words_local (hj : D.j=I.j) (hJ : D.J=I.J)
    (x : Spin n)
    (hW : w x=I.sourceOf 1 (fun _=>y) x)
    (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
    (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i))
    (ha0 : ∀i,0≤I.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
      (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef)
    {C F A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (hP : TraceControl (I.implicitSourcePrimitive t y x) C)
    (hQ : TraceControl (I.implicitFieldPrimitive t w y x) F)
    (hR : 0≤R) (hM : 0≤M) (ha : ∀i,|I.implicitCoefficient x i|≤A)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,0<a→TraceControl (D.startedNodeSourceError w y T x a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (D.startedNodeFieldError w y T x a) (Cf a))
    (hw : ClosedWordTestBound D.j (I.implicitCoefficient x) D.J A M (L+2)) :
    let t₀:=ClosedTree.implicit (I.implicitPartial y x) t
    let a₀:=I.implicitCoefficient x
    let q:=I.j*siteMean I.implicitCoefficient x
    let Bs:=fun a=>if a=0 then C+F else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+F)+F else Cf a
    ∀a≤N,
      (∀v:OrdinaryWord n,v.length+2*a+1≤L→wordBounded A v→
        |trace (matrixWord D.J v*D.startedSourceError w y T t₀ a₀ x a)|≤(errorBudget R Bs Bf a).1*M) ∧
      (∀v:OrdinaryWord n,v.length+2*a+2≤L→wordBounded A v→
        |trace (matrixWord D.J v*D.startedFieldError w y T t₀ a₀ x a)|≤(errorBudget R Bs Bf a).2*M) := by
  obtain ⟨HE,HF⟩:=D.started_implicit_initial_errors_local I w y T t hj hJ x hW hWf hY hYf ha0 hS
  exact D.started_derivative_error_words w y T _ _ x
    (I.implicitSourcePrimitive t y x) (I.implicitFieldPrimitive t w y x)
    (I.j*siteMean I.implicitCoefficient x) HE HF hP hQ hR hM ha hp hr hs hf hw

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
