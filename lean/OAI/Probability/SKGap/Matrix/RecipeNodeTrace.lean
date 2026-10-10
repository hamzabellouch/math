import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Stability.OrdinaryGraph
import OAI.Probability.SKGap.Matrix.PrimitiveTrace
import OAI.Probability.SKGap.Localization.RecipeError

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

def nodeSourceError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  D.sourceAtoms a (fun b=>D.auxiliary b) x+
  ∑l,Matrix.diagonal (D.sourcePartial a l x)*
    (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l))
def nodeFieldError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  -(∑l,(D.j*siteMean (D.sourcePartial a l) x) •
    (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))-
  D.j • ((∑l,averageError (siteMean (D.sourcePartial a l)) (D.predecessor l) x)+
    ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.source b) x)

lemma source_error_nodes (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.sourceDerivativeError T x a=
      (∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.fieldDerivativeError T x b)+
      D.nodeSourceError T x a := by
  rw [D.source_error_recursion,nodeSourceError]; abel
lemma field_error_nodes (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.fieldDerivativeError T x a=D.J*D.sourceDerivativeError T x a-
      (∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.sourceDerivativeError T x b)+
      D.nodeFieldError T x a := by
  rw [D.field_error_recursion,nodeFieldError]; abel

lemma nodeSource_control (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ)
    {C Q R L V Z : ℝ} {B : Fin a→ℝ} {Cp E : ι→ℝ}
    (hC : 0≤C) (hQ : 0≤Q) (hR : 0≤R) (hL : 0≤L) (hV : 0≤V)
    (hY : ∀b:Fin a,SmallBound (D.auxiliary b) x (B b))
    (hp : ∀l,SmallBound (D.sourcePartial a l) x (Cp l))
    (hE : ∀l,‖derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)‖≤E l)
    (hs : ∀s,SegmentRegular D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) x C)
    (ha : ∀b,SegmentRegular D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) x C)
    (ht : vectorNorm (parameterIncrement D.θ x)≤V)
    (hQ4 : (∑i,∑k,(primaryIncrement D.H x i k)^4)≤Q^4)
    (hQr : ∀i,(∑k,(primaryIncrement D.H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement D.H x i i)^2)≤L^2)
    (hZ : (∑α,‖derivativeVector (D.θ α) x‖)+4*(Q^2+R*V+V^2)+2*(Q+L+V)≤Z) :
    TraceControl (D.nodeSourceError T x a)
      (((∑s,C*vectorNorm (D.seed s)*Z)+(∑b:Fin a,C*B b*Z))+∑l,Cp l*E l) := by
  have hc (s : VectorFields n) {S : ℝ} (hS : SmallBound s x S)
      (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
      (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
      (hF : SegmentRegular D.H D.θ F F' x C) : TraceControl (sourceError D.H D.θ F F' s x) (C*S*Z) :=
    (sourceError_control D.H D.θ F F' s x hF hS.nonneg hV hQ hR hL hS.size hS.derivative ht hQ4 hQr hQd).mono
      (mul_le_mul_of_nonneg_left hZ (mul_nonneg hC hS.nonneg))
  have hs' := TraceControl.sum (fun s=>hc (fun _=>D.seed s) (SmallBound.seed _ x) _ _ (hs s))
  have ha' := TraceControl.sum (fun b:Fin a=>hc (D.auxiliary b) (hY b) _ _ (ha b))
  have hp' := TraceControl.sum (fun l=>(small_diagonal_control
    (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)) (D.sourcePartial a l x)).mono
      (mul_le_mul (hp l).size (hE l) (norm_nonneg _) (hp l).nonneg))
  exact (hs'.add ha').add hp'

lemma nodeField_control (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) (hn : 0<n)
    {P R : ℝ} {B : Fin a→ℝ} {Cp E : ι→ℝ} (hP : 0≤P) (hR : 0≤R)
    (hW : ∀b:Fin a,SmallBound (D.source b) x (B b))
    (hp : ∀l,SmallBound (D.sourcePartial a l) x (Cp l))
    (hE : ∀l,‖derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)‖≤E l)
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (hda : ∀b i,∑k,(derivativeMatrix (D.auxCoefficient a b) x i k)^2≤R^2) :
    TraceControl (D.nodeFieldError T x a)
      ((∑l,|D.j| *(Cp l*E l))+|D.j| *((∑l,Cp l*(1+2*P))+(∑b:Fin a,3*B b*R))) := by
  have hmE (l : ι) : TraceControl
      ((D.j*siteMean (D.sourcePartial a l) x) •
        (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))
      (|D.j| *(Cp l*E l)) := by
    simpa only [smul_smul] using ((small_mean_control
      (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l))
      (D.sourcePartial a l) x hn).mono
        (mul_le_mul (hp l).size (hE l) (norm_nonneg _) (hp l).nonneg)).smul D.j
  have hpE (l : ι) := primary_averageError_control (D.sourcePartial a l) (D.predecessor l) x hn
    (hp l).nonneg hP (hp l).derivative (hm l) (hdm l)
  have haE (b : Fin a) : TraceControl (averageError (siteMean (D.auxCoefficient a b)) (D.source b) x) (3*B b*R) := by
    apply (averageError_control (siteMean (D.auxCoefficient a b)) (D.source b) x).mono
    have H:=coefficient_mean_difference (D.auxCoefficient a b) x hR (hda b)
    have h1 := add_le_add (hW b).size (mul_le_mul_of_nonneg_left (hW b).derivative (by norm_num : (0:ℝ)≤2))
    exact (mul_le_mul h1 H (norm_nonneg _) (by linarith [(hW b).nonneg])).trans_eq (by ring)
  exact (TraceControl.sum hmE).neg.sub (((TraceControl.sum hpE).add (TraceControl.sum haE)).smul D.j)

theorem derivative_error_words (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n)
    {N L : ℕ} {A R M : ℝ} {Cs Cf : ℕ→ℝ} (hR : 0≤R) (hM : 0≤M)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,TraceControl (D.nodeSourceError T x a) (Cs a))
    (hf : ∀a≤N,TraceControl (D.nodeFieldError T x a) (Cf a))
    (hw : WordTestBound D.J A M L) :
    ∀a≤N,
      (∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (SKGap.Noncrossing.Primary.matrixWord D.J w*D.sourceDerivativeError T x a)|≤(errorBudget R Cs Cf a).1*M) ∧
      (∀w:OrdinaryWord n,w.length+2*a+2≤L→wordBounded A w→
        |trace (SKGap.Noncrossing.Primary.matrixWord D.J w*D.fieldDerivativeError T x a)|≤(errorBudget R Cs Cf a).2*M) :=
  finite_graph_trace D.J (D.sourceDerivativeError T x) (D.fieldDerivativeError T x)
    (D.nodeSourceError T x) (D.nodeFieldError T x) (fun a b=>D.auxCoefficient a b x)
    (fun a b=>D.j*siteMean (D.auxCoefficient a b) x)
    (D.source_error_nodes T x) (D.field_error_nodes T x) hR hM hp hr hs hf hw

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
