import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryWordEvent
import OAI.Probability.SKGap.Matrix.StartedTraceBudget
import OAI.Probability.SKGap.Localization.ClosedMarkedControl
import OAI.Probability.SKGap.Localization.StartedSmall

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ}

def ClosedWordDiagramBound (j : ℝ) (a : Fin n→ℝ) (J : Interaction n) (A B : ℝ) (L : ℕ) : Prop :=
  ∀w:List (WordLetter (Fin n)),w.length≤L→inverseCount w≤1→closedWordBounded A w→
    diagonalSeminorm (exactWord j a w J-Matrix.diagonal (wordPrediction j a 1 w))≤B

def initialTraceBudget (j A B Q : ℝ) : ℝ := (2+|j| *A)*(B*((1+|j|)*Q))+|j| *B*Q
lemma initialTraceBudget_nonneg {j A B Q : ℝ} (hA : 0≤A) (hB : 0≤B) (hQ : 0≤Q) :
    0≤ initialTraceBudget j A B Q := by unfold initialTraceBudget;positivity

namespace OrdinaryData
variable {ι κ σ κ₀ σ₀ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable (D : OrdinaryData n ι κ σ) (I : OrdinaryData n Unit κ₀ σ₀)

theorem implicit_started_word_closure (w y : VectorFields n) (T : ι→SourceTree (Fin n→ℝ)) (t : SourceTree (Fin n→ℝ))
    (hj : D.j=I.j) (hJ : D.J=I.J) (x : Spin n) (N L : ℕ) (c : LocalConstants)
    (h : LocalOrdinaryInput D T x N c)
    (hW : w x=I.sourceOf 1 (fun _=>y) x) (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
    (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x) (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i))
    (ha0 : ∀i,0≤I.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
      (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef)
    {C F B₀ M B Q : ℝ} (hB₀ : 0≤B₀) (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
    (hw₀ : SmallBound w x B₀) (hy₀ : SmallBound y x B₀) (hp₀ : vectorNorm (I.implicitPartial y x)≤B₀)
    (hP : TraceControl (I.implicitSourcePrimitive t y x) C)
    (hF : TraceControl (I.implicitFieldPrimitive t w y x) F)
    (ha : ∀i,|I.implicitCoefficient x i|≤c.A)
    (hm : ∀l,Marked.mass (GradedWords.ordinaryWords D.j (T l)).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords D.j (T l)).2≤Q)
    (hm₀ : Marked.mass (GradedWords.ordinaryWords D.j t).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords D.j t).2≤Q)
    (hT : ∀l,GradedControl c.A L (GradedWords.ordinaryWords D.j (T l)).1 ∧ GradedControl c.A L (GradedWords.ordinaryWords D.j (T l)).2)
    (ht : GradedControl c.A L (GradedWords.ordinaryWords D.j t).1 ∧ GradedControl c.A L (GradedWords.ordinaryWords D.j t).2)
    (hw : ClosedWordTestBound D.j (I.implicitCoefficient x) D.J c.A M (2*N+5))
    (hd : ClosedWordDiagramBound D.j (I.implicitCoefficient x) D.J c.A B (L+2*N+3)) :
    let W:=c.startedNormBudget D.j (Fintype.card ι) B₀
    let R:=errorBudget (|D.j| *c.A)
      (fun a=>if a=0 then C+F else c.startedSourceCost D.j (Fintype.card ι) (Fintype.card σ) B₀ a)
      (fun a=>if a=0 then |I.j*siteMean I.implicitCoefficient x| *(C+F)+F else c.startedFieldCost D.j (Fintype.card ι) B₀ a)
    let V:=startedTraceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W (initialTraceBudget D.j c.A B₀ Q)
    ∀a≤N,SmallBound (D.startedSource w y a) x (W a) ∧
      (∀l,SmallBound (D.startedPartial w y a l) x (W a)) ∧
      (∑i,|derivativeMatrix (D.startedSource w y a) x i i|)≤V a*B+(R a).1*M := by
  dsimp only
  let t₀:SmallTree n:=.implicit (I.implicitPartial y x) t
  let a₀:=I.implicitCoefficient x
  let W:=c.startedNormBudget D.j (Fintype.card ι) B₀
  have hwsmall:=h.started_small hB₀ hw₀ hy₀
  have htrace:=D.implicit_started_diagonal_local I w y T t hj hJ x hW hWf hY hYf h.dimension ha0 hS hP hF
    (mul_nonneg (abs_nonneg _) c.A_nonneg) hM hB c.one_le_A ha h.auxValue
    (fun a haN b=>by rw [abs_mul];exact mul_le_mul_of_nonneg_left (h.mean_bound a haN b) (abs_nonneg _))
    (fun a haN _=>h.started_source_control hB₀ hw₀ hy₀ a haN)
    (fun a haN _=>h.started_field_control hB₀ hw₀ hy₀ a haN) hw (by
      intro a haN d hd' P hP' v hv
      have hc:=D.startedMarked_control w y T t₀ a₀ x N L c.one_le_A
        (implicitPair_control D.j a₀ _ t c.one_le_A ha ht) hT h.auxValue a haN
      have hcontrol : SKGap.Noncrossing.ClosedMarked.MarkControl c.A (L+2*a+3) v.2 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hP'
        rcases hP' with rfl|rfl
        · exact hc.1 v hv
        · exact hc.2 v hv
      have hinv : inverseCount (v.2.diagnostic d)≤1 := by
        rw [Mark.diagnostic_inverse]
        have hb:=(D.startedSmallTree w y T t₀ x a).plain D.j a₀
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hP'
        rcases hP' with rfl|rfl
        · exact Marked.bounded_of_plain _ _ (congrArg Prod.fst hb)
            ((D.startedSmallTree w y T t₀ x a).tree.words_bounded D.j a₀).1 v hv
        · exact Marked.bounded_of_plain _ _ (congrArg Prod.snd hb)
            ((D.startedSmallTree w y T t₀ x a).tree.words_bounded D.j a₀).2 v hv
      exact hd _ ((hcontrol d hd').2.trans (by omega)) hinv (hcontrol d hd').1)
  have hi:pairBudget (t₀.marked D.j a₀)≤ initialTraceBudget D.j c.A B₀ Q := by
    apply implicitPair_budget_le D.j a₀ _ t hp₀ hQ hm₀
    simpa only [siteMean,Diagram.mean,Fintype.card_fin] using coefficient_mean_value I.implicitCoefficient x c.A_nonneg ha
  have hb:=D.startedMarked_budget w y T t₀ a₀ x N W c.A_nonneg hQ
    (initialTraceBudget_nonneg c.A_nonneg hB₀ hQ) (fun a=>c.startedNormBudget_nonneg D.j _ a hB₀)
    hi (fun a haN l=>(hwsmall a haN).2.2 l |>.size) hm h.mean_bound
  intro a haN
  have haB: ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).1.budget≤
      startedTraceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W (initialTraceBudget D.j c.A B₀ Q) a :=
    (le_add_of_nonneg_right (Marked.budget_nonneg _)).trans (hb a haN)
  exact ⟨(hwsmall a haN).1,(hwsmall a haN).2.2,
    ((htrace a haN).1).trans (add_le_add (mul_le_mul_of_nonneg_right haB hB) le_rfl)⟩
end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma closedWordBounded_iff (A : ℝ) (w : List (WordLetter (Fin n))) :
    closedWordBounded A w ↔ ∀l∈w,l.bounded A := by
  constructor <;> intro h l hl <;> cases l <;> exact h _ hl

def ClosedWordSeminormBound (j : ℝ) (a : Fin n→ℝ) (J : Interaction n)
    (A C : ℝ) (L : ℕ) : Prop :=
  ∀(p : Bool) (w : List (WordLetter (Fin n))),w.length≤L→inverseCount w≤1→closedWordBounded A w→
    matrixWordSeminorm p (exactWord j a w J-Matrix.diagonal (wordPrediction j a 1 w))≤C

lemma ClosedWordSeminormBound.mono {j A C : ℝ} {a : Fin n→ℝ} {J : Interaction n} {L K : ℕ}
    (h : ClosedWordSeminormBound j a J A C L) (hK : K≤L) :
    ClosedWordSeminormBound j a J A C K := fun p w hw hi hb=>h p w (hw.trans hK) hi hb

lemma ClosedWordSeminormBound.diagram {j A C : ℝ} {a : Fin n→ℝ} {J : Interaction n} {L : ℕ}
    (h : ClosedWordSeminormBound j a J A C L) : ClosedWordDiagramBound j a J A C L := h false

def ClosedWordEvent (j A D c C : ℝ) (L : ℕ) (J : Interaction n) : Prop :=
  ∀a:Fin n→ℝ,(∀i,a i∈Icc 0 A)→
    c≤ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))→
    ClosedWordSeminormBound j a J D C L

theorem closed_word_event {j A D c : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0<c) (L : ℕ) :
    ∃(C : ℝ) (N : ℕ),0<C ∧ 0<N ∧ ∀n,N≤n→
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ¬ClosedWordEvent j A D c C L (removeDiagonal (goeMatrix (j/n) g))}≤
      2*((wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
        ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))+
        (ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
          ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n)))))) := by
  obtain ⟨C,N,hC,hN,hb⟩:=zeroDiag_exact_words_two_seminorms hj hA hs hD hAD hc L
  refine ⟨C,N,hC,hN,fun n hn=>?_⟩
  apply (measure_mono ?_).trans (hb n hn)
  intro g hg
  simp only [ClosedWordEvent,ClosedWordSeminormBound,not_forall,not_le] at hg
  obtain ⟨a,ha,hstable,p,w,hw,hi,hwb,hfail⟩:=hg
  exact ⟨p,a,w,ha,hw,(closedWordBounded_iff D w).mp hwb,hi,Or.inr hstable,hfail⟩

theorem closed_word_test_budget {j A D c R : ℝ} (hj : 0≤j) (hA : 0≤A)
    (hD : 0≤D) (hc : 0<c) (hR : 0≤R) (L : ℕ) :
    ∃W : ℝ,0<W ∧ ∀n,0<n→∀(a:Fin n→ℝ) (J:Interaction n) (C:ℝ),
      (∀i,a i∈Icc 0 A)→Jᵀ=J→SKGap.opNorm J≤R→
      c≤ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))→
      ClosedWordSeminormBound j a J D C L→ClosedWordTestBound j a J D (W+C) L := by
  obtain ⟨W,hW,hw⟩:=exactWord_uniform_opNorm hj hA hD hc hR L
  refine ⟨W,hW,?_⟩
  intro n hn a J C ha hJ hR' hs hb w hl hi hwb
  have hop:=hw n hn a w J ha hl ((closedWordBounded_iff D w).mp hwb) hJ hR' (Or.inr hs)
  have hoff:=hb true w hl hi hwb
  simp only [matrixWordSeminorm,↓reduceIte,offDiagonalSeminorm_sub_diagonal] at hoff
  exact add_le_add hop hoff

end SKGapCutoff.Recipe

end
end

end OAI
