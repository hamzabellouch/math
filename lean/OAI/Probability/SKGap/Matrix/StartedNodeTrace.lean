import Mathlib
import OAI.Probability.SKGap.Stability.StableFields
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Matrix.ClosedErrorTrace
import OAI.Probability.SKGap.Localization.StartedGraph

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)

def startedNodeSourceError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  D.sourceAtoms a (fun b=>D.startedAuxiliary w y b) x+
  ∑l,Matrix.diagonal (D.startedPartial w y a l x)*
    (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l))
def startedNodeFieldError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  -(∑l,(D.j*siteMean (D.startedPartial w y a l) x) •
    (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))-
  D.j • ((∑l,averageError (siteMean (D.startedPartial w y a l)) (D.predecessor l) x)+
    ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.startedSource w y b) x)

lemma startedNodeSource_control (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ)
    {C Q R L V Z : ℝ} {B : Fin a→ℝ} {Cp E : ι→ℝ}
    (hC : 0≤C) (hQ : 0≤Q) (hR : 0≤R) (hL : 0≤L) (hV : 0≤V)
    (hY : ∀b:Fin a,SmallBound (D.startedAuxiliary w y b) x (B b))
    (hp : ∀l,SmallBound (D.startedPartial w y a l) x (Cp l))
    (hE : ∀l,‖derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)‖≤E l)
    (hs : ∀s,SegmentRegular D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) x C)
    (ha : ∀b,SegmentRegular D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) x C)
    (ht : vectorNorm (parameterIncrement D.θ x)≤V)
    (hQ4 : (∑i,∑k,(primaryIncrement D.H x i k)^4)≤Q^4)
    (hQr : ∀i,(∑k,(primaryIncrement D.H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement D.H x i i)^2)≤L^2)
    (hZ : (∑α,‖derivativeVector (D.θ α) x‖)+4*(Q^2+R*V+V^2)+2*(Q+L+V)≤Z) :
    TraceControl (D.startedNodeSourceError w y T x a)
      (((∑s,C*vectorNorm (D.seed s)*Z)+(∑b:Fin a,C*B b*Z))+∑l,Cp l*E l) := by
  have hc (s : VectorFields n) {S : ℝ} (hS : SmallBound s x S)
      (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
      (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
      (hF : SegmentRegular D.H D.θ F F' x C) : TraceControl (sourceError D.H D.θ F F' s x) (C*S*Z) :=
    (sourceError_control D.H D.θ F F' s x hF hS.nonneg hV hQ hR hL hS.size hS.derivative ht hQ4 hQr hQd).mono
      (mul_le_mul_of_nonneg_left hZ (mul_nonneg hC hS.nonneg))
  have hs' := TraceControl.sum (fun s=>hc (fun _=>D.seed s) (SmallBound.seed _ x) _ _ (hs s))
  have ha' := TraceControl.sum (fun b:Fin a=>hc (D.startedAuxiliary w y b) (hY b) _ _ (ha b))
  have hp' := TraceControl.sum (fun l=>(small_diagonal_control
    (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)) (D.startedPartial w y a l x)).mono
      (mul_le_mul (hp l).size (hE l) (norm_nonneg _) (hp l).nonneg))
  exact (hs'.add ha').add hp'

lemma startedNodeField_control (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) (hn : 0<n)
    {P R : ℝ} {B : Fin a→ℝ} {Cp E : ι→ℝ} (hP : 0≤P) (hR : 0≤R)
    (hW : ∀b:Fin a,SmallBound (D.startedSource w y b) x (B b))
    (hp : ∀l,SmallBound (D.startedPartial w y a l) x (Cp l))
    (hE : ∀l,‖derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)‖≤E l)
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (hda : ∀b i,∑k,(derivativeMatrix (D.auxCoefficient a b) x i k)^2≤R^2) :
    TraceControl (D.startedNodeFieldError w y T x a)
      ((∑l,|D.j| *(Cp l*E l))+|D.j| *((∑l,Cp l*(1+2*P))+(∑b:Fin a,3*B b*R))) := by
  have hmE (l : ι) : TraceControl
      ((D.j*siteMean (D.startedPartial w y a l) x) •
        (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))
      (|D.j| *(Cp l*E l)) := by
    simpa only [smul_smul] using ((small_mean_control
      (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l))
      (D.startedPartial w y a l) x hn).mono
        (mul_le_mul (hp l).size (hE l) (norm_nonneg _) (hp l).nonneg)).smul D.j
  have hpE (l : ι) := primary_averageError_control (D.startedPartial w y a l) (D.predecessor l) x hn
    (hp l).nonneg hP (hp l).derivative (hm l) (hdm l)
  have haE (b : Fin a) : TraceControl (averageError (siteMean (D.auxCoefficient a b)) (D.startedSource w y b) x) (3*B b*R) := by
    apply (averageError_control (siteMean (D.auxCoefficient a b)) (D.startedSource w y b) x).mono
    have H:=coefficient_mean_difference (D.auxCoefficient a b) x hR (hda b)
    have h1 := add_le_add (hW b).size (mul_le_mul_of_nonneg_left (hW b).derivative (by norm_num : (0:ℝ)≤2))
    exact (mul_le_mul h1 H (norm_nonneg _) (by linarith [(hW b).nonneg])).trans_eq (by ring)
  exact (TraceControl.sum hmE).neg.sub (((TraceControl.sum hpE).add (TraceControl.sum haE)).smul D.j)

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (a₀ : Fin n→ℝ) (x : Spin n)

theorem started_derivative_error_words (P Q : Interaction n) (q : ℝ)
    (hE₀ : D.startedSourceError w y T t₀ a₀ x 0=
      WordLetter.inverse.exactEval D.j a₀ D.J*(P+Matrix.diagonal a₀*Q))
    (hF₀ : D.startedFieldError w y T t₀ a₀ x 0=
      (D.J-q • 1)*D.startedSourceError w y T t₀ a₀ x 0+Q)
    {C F A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (hP : TraceControl P C) (hQ : TraceControl Q F)
    (hR : 0≤R) (hM : 0≤M) (ha : ∀i,|a₀ i|≤A)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,0<a→TraceControl (D.startedNodeSourceError w y T x a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (D.startedNodeFieldError w y T x a) (Cf a))
    (hw : ClosedWordTestBound D.j a₀ D.J A M (L+2)) :
    let Bs:=fun a=>if a=0 then C+F else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+F)+F else Cf a
    ∀a≤N,
      (∀v:OrdinaryWord n,v.length+2*a+1≤L→wordBounded A v→
        |trace (matrixWord D.J v*D.startedSourceError w y T t₀ a₀ x a)|≤(errorBudget R Bs Bf a).1*M) ∧
      (∀v:OrdinaryWord n,v.length+2*a+2≤L→wordBounded A v→
        |trace (matrixWord D.J v*D.startedFieldError w y T t₀ a₀ x a)|≤(errorBudget R Bs Bf a).2*M) := by
  let Es:=fun a=>if a=0 then D.startedSourceError w y T t₀ a₀ x 0 else D.startedNodeSourceError w y T x a
  let Ef:=fun a=>if a=0 then (-q) • Es 0+Q else D.startedNodeFieldError w y T x a
  apply closed_finite_graph_trace D.j a₀ D.J
    (D.startedSourceError w y T t₀ a₀ x) (D.startedFieldError w y T t₀ a₀ x)
    Es Ef P Q q (fun a b=>D.auxCoefficient a b x) (fun a b=>D.j*siteMean (D.auxCoefficient a b) x)
    _ _ _ _ hP hQ hR hM ha hp hr _ _ hw
  · intro a
    by_cases ha0:a=0
    · subst a;simp [Es]
    · rw [D.started_source_error_recursion w y T t₀ a₀ x (Nat.pos_of_ne_zero ha0)]
      simp only [Es,ite_eq_right ha0,startedNodeSourceError]
      abel
  · intro a
    by_cases ha0:a=0
    · subst a
      simp only [Ef,Es,ite_true,Finset.univ_eq_empty,Finset.sum_empty,sub_zero]
      rw [hF₀,sub_mul,smul_mul_assoc,one_mul,neg_smul]
      abel
    · rw [D.started_field_error_recursion w y T t₀ a₀ x (Nat.pos_of_ne_zero ha0)]
      simp only [Ef,ite_eq_right ha0,startedNodeFieldError]
  · simpa only [Es,ite_true] using hE₀
  · rfl
  · intro a haN ha0;simpa only [Es,ite_eq_right (by omega : a≠0)] using hs a haN ha0
  · intro a haN ha0;simpa only [Ef,ite_eq_right (by omega : a≠0)] using hf a haN ha0

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
