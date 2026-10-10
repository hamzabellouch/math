import Mathlib
import OAI.Probability.SKGap.Localization.RecipeError
import OAI.Probability.SKGap.Matrix.PrimitiveTrace
import OAI.Probability.SKGap.Localization.RecipeIncrement
import OAI.Probability.SKGap.Localization.RecipeBound
import OAI.Probability.SKGap.Matrix.RecipeTraceBudget
import OAI.Probability.SKGap.Matrix.RecipeNodeTrace

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial

structure LocalConstants where
  A : ℝ
  C : ℝ
  P : ℝ
  L : ℝ
  E : ℝ
  V : ℝ
  S : ℝ
  one_le_A : 1≤A
  C_nonneg : 0≤C
  C_le_A : C≤A
  P_nonneg : 0≤P
  L_nonneg : 0≤L
  E_nonneg : 0≤E
  V_nonneg : 0≤V
  S_nonneg : 0≤S

namespace LocalConstants
variable (c : LocalConstants)
def argument (d : ℕ) : ℝ := (d:ℝ)*c.P+c.V
def row (d : ℕ) : ℝ := c.C*c.argument d
def normBudget (j : ℝ) (d : ℕ) : ℕ→ℝ := recipeBudget (recipeCost c.A (c.row d) c.L c.P j d) c.S
def traceCost (d : ℕ) : ℝ :=
  c.V+4*((2*(d:ℝ)*c.P)^2+((d:ℝ)*c.P)*c.V+c.V^2)+2*(2*(d:ℝ)*c.P+(d:ℝ)*c.P+c.V)
def sourceCost (j : ℝ) (d s : ℕ) (a : ℕ) : ℝ :=
  (s:ℝ)*(c.C*c.S*c.traceCost d)+(∑b:Fin a,c.C*c.normBudget j d b*c.traceCost d)+
    (d:ℝ)*(c.normBudget j d a*c.E)
def fieldCost (j : ℝ) (d : ℕ) (a : ℕ) : ℝ :=
  (d:ℝ)*(|j| *(c.normBudget j d a*c.E))+
    |j| *((d:ℝ)*(c.normBudget j d a*(1+2*c.P))+(∑b:Fin a,3*c.normBudget j d b*c.row d))
lemma A_nonneg : 0≤c.A := le_trans (by norm_num) c.one_le_A
lemma argument_nonneg (d : ℕ) : 0≤c.argument d := by unfold argument; positivity [c.P_nonneg,c.V_nonneg]
lemma row_nonneg (d : ℕ) : 0≤c.row d := mul_nonneg c.C_nonneg (c.argument_nonneg d)
lemma normBudget_nonneg (j : ℝ) (d a : ℕ) : 0≤c.normBudget j d a :=
  recipeBudget_nonneg (recipeCost_nonneg c.A_nonneg (c.row_nonneg d) c.L_nonneg c.P_nonneg) c.S_nonneg a
lemma traceCost_nonneg (d : ℕ) : 0≤c.traceCost d := by unfold traceCost; positivity [c.P_nonneg,c.V_nonneg]
end LocalConstants

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

structure LocalOrdinaryInput (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (N : ℕ) (c : LocalConstants) : Prop where
  dimension : 0<n
  interaction : SKGap.opNorm D.J≤c.L
  primaryShape : ∀l,ShapeBound (derivativeMatrix (D.H l) x) c.P
  primaryFieldError : ∀l,‖derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)‖≤c.E
  primarySourceError : ∀l,‖derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)‖≤c.E
  primaryValue : ∀l i,|D.predecessor l x i|≤1
  primaryDerivative : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤c.P
  seed : (∑s,vectorNorm (D.seed s))≤c.S
  parameter : (∑α,‖derivativeVector (D.θ α) x‖)≤c.V
  seedRegular : ∀a≤N,∀s,SegmentRegular D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) x c.C
  auxRegular : ∀a≤N,∀b,SegmentRegular D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) x c.C
  seedValue : ∀a≤N,∀s i,|D.seedCoefficient a s x i|≤c.A
  auxValue : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤c.A

namespace LocalOrdinaryInput
variable {D : OrdinaryData n ι κ σ} {T : ι→SourceTree (Fin n→ℝ)}
variable {x : Spin n} {N : ℕ} {c : LocalConstants}
variable (h : LocalOrdinaryInput D T x N c)
include h

lemma argument_bound : (∑l,SKGap.opNorm (derivativeMatrix (D.H l) x))+
    (∑α,‖derivativeVector (D.θ α) x‖)≤c.argument (Fintype.card ι) := by
  apply add_le_add _ h.parameter
  exact (Finset.sum_le_sum fun l _=>(h.primaryShape l).1).trans_eq (by simp)
lemma seed_bound (a : ℕ) (ha : a≤N) (s : σ) :
    CoefficientBound (D.seedCoefficient a s) x c.A (c.row (Fintype.card ι)) :=
  (h.seedRegular a ha s).coefficient_bound c.A_nonneg (c.argument_nonneg _) (h.seedValue a ha s) h.argument_bound
lemma aux_bound (a : ℕ) (ha : a≤N) (b : Fin a) :
    CoefficientBound (D.auxCoefficient a b) x c.A (c.row (Fintype.card ι)) :=
  (h.auxRegular a ha b).coefficient_bound c.A_nonneg (c.argument_nonneg _) (h.auxValue a ha b) h.argument_bound
lemma seed_partial_bound (a : ℕ) (ha : a≤N) (l : ι) (s : σ) :
    CoefficientBound (D.seedPartial a l s) x c.A (c.row (Fintype.card ι)) :=
  (h.seedRegular a ha s).partial_bound_coefficient (.inl l) c.A_nonneg (c.argument_nonneg _) c.C_le_A h.argument_bound
lemma aux_partial_bound (a : ℕ) (ha : a≤N) (l : ι) (b : Fin a) :
    CoefficientBound (D.auxPartial a l b) x c.A (c.row (Fintype.card ι)) :=
  (h.auxRegular a ha b).partial_bound_coefficient (.inl l) c.A_nonneg (c.argument_nonneg _) c.C_le_A h.argument_bound

lemma small (a : ℕ) (ha : a≤N) :
    SmallBound (D.source a) x (c.normBudget D.j (Fintype.card ι) a) ∧
    SmallBound (D.auxiliary a) x (c.normBudget D.j (Fintype.card ι) a) ∧
    ∀l,SmallBound (D.sourcePartial a l) x (c.normBudget D.j (Fintype.card ι) a) :=
  D.evaluation_small N x h.dimension c.A_nonneg (c.row_nonneg _) c.L_nonneg c.P_nonneg c.S_nonneg
    h.interaction h.seed h.primaryValue h.primaryDerivative h.seed_bound h.aux_bound h.seed_partial_bound h.aux_partial_bound a ha

lemma source_control (a : ℕ) (ha : a≤N) :
    TraceControl (D.nodeSourceError T x a) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ) a) := by
  let d:=Fintype.card ι
  let W:=c.normBudget D.j d
  have hn (s : σ) : vectorNorm (D.seed s)≤c.S :=
    (Finset.single_le_sum (fun s _=>vectorNorm_nonneg (D.seed s)) (Finset.mem_univ s)).trans h.seed
  have H:=D.nodeSource_control T x a c.C_nonneg
    (show 0≤2*(d:ℝ)*c.P by positivity [c.P_nonneg])
    (show 0≤(d:ℝ)*c.P by positivity [c.P_nonneg])
    (show 0≤(d:ℝ)*c.P by positivity [c.P_nonneg]) c.V_nonneg
    (fun b:Fin a=>(h.small b (b.isLt.le.trans ha)).2.1) (h.small a ha).2.2 h.primaryFieldError
    (h.seedRegular a ha) (h.auxRegular a ha)
    ((parameterIncrement_bound D.θ x).trans h.parameter)
    (primaryIncrement_fourth D.H x c.P_nonneg h.primaryShape)
    (primaryIncrement_row D.H x c.P_nonneg (fun l=>(h.primaryShape l).1))
    (primaryIncrement_diagonal D.H x c.P_nonneg (fun l=>(h.primaryShape l).2.1))
    (show _≤c.traceCost d from add_le_add (add_le_add h.parameter le_rfl) le_rfl)
  apply H.mono
  have hs : (∑s,c.C*vectorNorm (D.seed s)*c.traceCost d)≤(Fintype.card σ:ℝ)*(c.C*c.S*c.traceCost d) :=
    (Finset.sum_le_sum fun s _=>mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hn s) c.C_nonneg) (c.traceCost_nonneg d)).trans_eq (by simp)
  dsimp only [LocalConstants.sourceCost]
  have hp : (∑_l:ι,c.normBudget D.j d a*c.E)=(d:ℝ)*(c.normBudget D.j d a*c.E) := by simp [d]
  rw [hp]
  exact add_le_add (add_le_add hs le_rfl) le_rfl

lemma field_control (a : ℕ) (ha : a≤N) :
    TraceControl (D.nodeFieldError T x a) (c.fieldCost D.j (Fintype.card ι) a) := by
  have H:=D.nodeField_control T x a h.dimension c.P_nonneg (c.row_nonneg _)
    (fun b:Fin a=>(h.small b (b.isLt.le.trans ha)).1) (h.small a ha).2.2 h.primarySourceError
    h.primaryValue h.primaryDerivative (fun b=>(h.aux_bound a ha b).difference)
  simpa only [LocalConstants.fieldCost,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using H

lemma mean_bound (a : ℕ) (ha : a≤N) (b : Fin a) : |siteMean (D.auxCoefficient a b) x|≤c.A :=
  coefficient_mean_value (D.auxCoefficient a b) x c.A_nonneg (h.auxValue a ha b)

end LocalOrdinaryInput

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

theorem ordinary_local_closure (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (N : ℕ)
    (c : LocalConstants) (h : LocalOrdinaryInput D T x N c)
    {M B Q : ℝ} (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀l,mass ((T l).words D.j).1≤Q ∧ mass ((T l).words D.j).2≤Q)
    (hw : WordTestBound D.J c.A M (2*N+3))
    (hd : ∀a≤N,∀d:Fin n→ℝ,(∀i,|d i|≤1)→
      (∀t∈(D.markedRecipe T x a).1,SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B) ∧
      (∀t∈(D.markedRecipe T x a).2,SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B)) :
    let W:=c.normBudget D.j (Fintype.card ι)
    let R:=errorBudget (|D.j| *c.A) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ))
      (c.fieldCost D.j (Fintype.card ι))
    let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W
    ∀a≤N,SmallBound (D.source a) x (W a) ∧ SmallBound (D.auxiliary a) x (W a) ∧
      (∑i,|derivativeMatrix (D.source a) x i i|)≤V a*B+(R a).1*M ∧
      (∑i,|derivativeMatrix (D.auxiliary a) x i i|)≤V a*B+(R a).2*M := by
  dsimp only
  let W:=c.normBudget D.j (Fintype.card ι)
  let R:=errorBudget (|D.j| *c.A) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ))
    (c.fieldCost D.j (Fintype.card ι))
  let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W
  have herr:=D.derivative_error_words T x (mul_nonneg (abs_nonneg _) c.A_nonneg) hM h.auxValue
    (fun a ha b=>by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.mean_bound a ha b) (abs_nonneg _))
    h.source_control h.field_control hw
  have hmark:=D.markedRecipe_budget T x N W c.A_nonneg hQ (fun a ha l=>(h.small a ha).2.2 l |>.size) hm h.mean_bound
  intro a ha
  have hbounds := h.small a ha
  have hretS : (∑i,|D.retainedSource T x a i i|)≤V a*B := by
    apply (D.retainedSource_diagonal T x a h.dimension hB (fun d hd'=>(hd a ha d hd').1)).trans
    apply mul_le_mul_of_nonneg_right _ hB
    exact (le_add_of_nonneg_right (budget_nonneg _)).trans (hmark a ha)
  have hretF : (∑i,|D.retainedField T x a i i|)≤V a*B := by
    apply (D.retainedField_diagonal T x a h.dimension hB (fun d hd'=>(hd a ha d hd').2)).trans
    apply mul_le_mul_of_nonneg_right _ hB
    exact (le_add_of_nonneg_left (budget_nonneg _)).trans (hmark a ha)
  have herrorS : (∑i,|D.sourceDerivativeError T x a i i|)≤(R a).1*M := by
    apply diagonal_abs_sum_of_tests
    intro d hd'
    have H:=(herr a ha).1 [.diag d] (by simp; omega) (by
      intro l hl; have he : l=Letter.diag d := List.mem_singleton.mp hl; subst l
      exact fun i=>(hd' i).trans c.one_le_A)
    simpa [matrixWord,matrixLetter] using H
  have herrorF : (∑i,|D.fieldDerivativeError T x a i i|)≤(R a).2*M := by
    apply diagonal_abs_sum_of_tests
    intro d hd'
    have H:=(herr a ha).2 [.diag d] (by simp; omega) (by
      intro l hl; have he : l=Letter.diag d := List.mem_singleton.mp hl; subst l
      exact fun i=>(hd' i).trans c.one_le_A)
    simpa [matrixWord,matrixLetter] using H
  refine ⟨hbounds.1,hbounds.2.1,?_,?_⟩
  · calc
      _ = ∑i,|D.retainedSource T x a i i+D.sourceDerivativeError T x a i i| := by
        simp only [sourceDerivativeError,Matrix.sub_apply]; congr 1; funext i; congr 1; ring
      _ ≤ (∑i,|D.retainedSource T x a i i|)+(∑i,|D.sourceDerivativeError T x a i i|) :=
        (Finset.sum_le_sum fun i _=>abs_add_le _ _).trans_eq Finset.sum_add_distrib
      _ ≤ _ := add_le_add hretS herrorS
  · calc
      _ = ∑i,|D.retainedField T x a i i+D.fieldDerivativeError T x a i i| := by
        simp only [fieldDerivativeError,Matrix.sub_apply]; congr 1; funext i; congr 1; ring
      _ ≤ (∑i,|D.retainedField T x a i i|)+(∑i,|D.fieldDerivativeError T x a i i|) :=
        (Finset.sum_le_sum fun i _=>abs_add_le _ _).trans_eq Finset.sum_add_distrib
      _ ≤ _ := add_le_add hretF herrorF

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
