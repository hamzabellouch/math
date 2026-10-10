import Mathlib
import OAI.Probability.SKGap.Matrix.PrimaryMatrix
import OAI.Probability.SKGap.Matrix.Trace
import OAI.Probability.SKGap.Matrix.CorrectionTrace

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}
local instance : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

def testSize (P : Interaction n) : ℝ := SKGap.opNorm P+SKGap.offDiagonalSeminorm P
lemma testSize_nonneg (P : Interaction n) : 0≤testSize P := add_nonneg (norm_nonneg _) (norm_nonneg _)
lemma opNorm_le_testSize (P : Interaction n) : SKGap.opNorm P≤testSize P := le_add_of_nonneg_right (norm_nonneg _)

structure TraceControl (E : Interaction n) (C : ℝ) : Prop where
  nonneg : 0≤C
  bound : ∀P,|trace (P*E)|≤C*testSize P

lemma TraceControl.zero : TraceControl (0 : Interaction n) 0 := by constructor <;> simp
lemma TraceControl.mono {E : Interaction n} {C D : ℝ} (h : TraceControl E C) (hCD : C≤D) : TraceControl E D :=
  ⟨h.nonneg.trans hCD,fun P=>(h.bound P).trans (mul_le_mul_of_nonneg_right hCD (testSize_nonneg P))⟩
lemma TraceControl.add {E F : Interaction n} {C D : ℝ} (hE : TraceControl E C) (hF : TraceControl F D) :
    TraceControl (E+F) (C+D) := by
  refine ⟨add_nonneg hE.nonneg hF.nonneg,?_⟩
  intro P; rw [mul_add,trace_add,add_mul]
  exact (abs_add_le _ _).trans (add_le_add (hE.bound P) (hF.bound P))
lemma TraceControl.smul {E : Interaction n} {C : ℝ} (hE : TraceControl E C) (a : ℝ) :
    TraceControl (a • E) (|a| *C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hE.nonneg,?_⟩
  intro P; rw [Matrix.mul_smul,trace_smul,smul_eq_mul,abs_mul]
  exact (mul_le_mul_of_nonneg_left (hE.bound P) (abs_nonneg a)).trans_eq (by ring)
lemma TraceControl.neg {E : Interaction n} {C : ℝ} (hE : TraceControl E C) : TraceControl (-E) C := by
  simpa using hE.smul (-1)
lemma TraceControl.sub {E F : Interaction n} {C D : ℝ} (hE : TraceControl E C) (hF : TraceControl F D) :
    TraceControl (E-F) (C+D) := by simpa only [sub_eq_add_neg] using hE.add hF.neg
lemma TraceControl.sum {α : Type*} [Fintype α] {E : α→Interaction n} {C : α→ℝ}
    (h : ∀a,TraceControl (E a) (C a)) : TraceControl (∑a,E a) (∑a,C a) := by
  refine ⟨Finset.sum_nonneg (fun a _=>(h a).nonneg),?_⟩
  intro P; rw [Matrix.mul_sum,trace_sum,Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun a _=>(h a).bound P)

lemma control_of_operator {E : Interaction n} {C : ℝ} (hC : 0≤C)
    (h : ∀P,|trace (P*E)|≤C*SKGap.opNorm P) : TraceControl E C :=
  ⟨hC,fun P=>(h P).trans (mul_le_mul_of_nonneg_left (opNorm_le_testSize P) hC)⟩

lemma small_diagonal_control (E : Interaction n) (u : Fin n→ℝ) :
    TraceControl (Matrix.diagonal u*E) (vectorNorm u*‖E‖) := by
  apply control_of_operator (mul_nonneg (vectorNorm_nonneg _) (norm_nonneg _))
  intro P; exact (trace_small_diagonal P E u).trans_eq (by ring)
lemma small_mean_control (E : Interaction n) (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    TraceControl (siteMean U x • E) (vectorNorm (U x)*‖E‖) := by
  apply control_of_operator (mul_nonneg (vectorNorm_nonneg _) (norm_nonneg _))
  intro P; exact (trace_small_mean P E U x hn).trans_eq (by ring)
lemma averageError_control (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    TraceControl (averageError a U x) ((vectorNorm (U x)+2*‖derivativeMatrix U x‖)*‖derivativeVector a x‖) := by
  apply control_of_operator (by positivity [vectorNorm_nonneg (U x)])
  intro P; exact (averageError_trace P a U x).trans_eq (by ring)
lemma primary_averageError_control (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    {C R : ℝ} (hC : 0≤C) (hR : 0≤R) (hU : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤R) :
    TraceControl (averageError (siteMean U) m x) (C*(1+2*R)) := by
  apply control_of_operator (by positivity)
  intro P; exact (primary_averageError_trace P U m x hn hC hR hU hm hdm).trans_eq (by ring)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma sourceError_control (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) {C S T B R L : ℝ}
    (h : SegmentRegular H θ F F' x C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R) (hL : 0≤L)
    (hs : vectorNorm (s x)≤S) (hds : ‖derivativeMatrix s x‖≤S)
    (ht : vectorNorm (parameterIncrement θ x)≤T)
    (hQ4 : (∑i,∑k,(primaryIncrement H x i k)^4)≤B^4)
    (hQr : ∀i,(∑k,(primaryIncrement H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement H x i i)^2)≤L^2) :
    TraceControl (sourceError H θ F F' s x)
      (C*S*((∑α,‖derivativeVector (θ α) x‖)+4*(B^2+R*T+T^2)+2*(B+L+T))) := by
  have hC := h.nonneg
  have hsum : 0≤∑α,‖derivativeVector (θ α) x‖ := Finset.sum_nonneg fun α _=>norm_nonneg _
  refine ⟨by positivity,?_⟩
  intro P
  have hO : 0≤SKGap.offDiagonalSeminorm P := norm_nonneg _
  have hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤SKGap.offDiagonalSeminorm P^4 := by
    rw [SKGap.offDiagonalSeminorm_fourth,Fintype.sum_prod_type,Finset.sum_comm]
    simp only [eq_comm]; rfl
  apply (sourceError_trace H θ F F' s x P h hS hT hB hR hL hO hs hds ht hQ4 hQr hQd hP).trans
  have h₁ : 0≤C*S*((∑α,‖derivativeVector (θ α) x‖)+4*(B^2+R*T+T^2)+2*(L+T)) := by positivity
  have h₂ : 0≤2*C*S*B := by positivity
  have H₁ := mul_nonneg (real_op_norm_nonneg P) h₂
  have H₂ := mul_nonneg hO h₁
  unfold testSize
  nlinarith only [H₁,H₂]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

abbrev OrdinaryWord (n : ℕ) := List (Letter (Fin n→ℝ))
def wordBounded (A : ℝ) (w : OrdinaryWord n) : Prop :=
  ∀l∈w,match l with | .diag p=>∀i,|p i|≤A | .noise=>True
lemma wordBounded_diag {A : ℝ} {w : OrdinaryWord n} (h : wordBounded A w)
    (p : Fin n→ℝ) (hp : ∀i,|p i|≤A) : wordBounded A (w++[.diag p]) := by
  intro l hl; rcases List.mem_append.mp hl with hl|hl
  · exact h l hl
  · have he : l=Letter.diag p := List.mem_singleton.mp hl; subst l; exact hp
lemma wordBounded_noise {A : ℝ} {w : OrdinaryWord n} (h : wordBounded A w) :
    wordBounded A (w++[.noise]) := by
  intro l hl; rcases List.mem_append.mp hl with hl|hl
  · exact h l hl
  · have he : l=Letter.noise := List.mem_singleton.mp hl; subst l; trivial

def WordTestBound (J : Interaction n) (A M : ℝ) (L : ℕ) : Prop :=
  ∀w:OrdinaryWord n,w.length≤L→wordBounded A w→testSize (matrixWord J w)≤M

def errorBudget (R : ℝ) (Cs Cf : ℕ→ℝ) (a : ℕ) : ℝ×ℝ :=
  let S:=Cs a+∑b:Fin a,(errorBudget R Cs Cf b).2
  (S,S+R*(∑b:Fin a,(errorBudget R Cs Cf b).1)+Cf a)
termination_by a
lemma errorBudget_nonneg {R : ℝ} (hR : 0≤R) {Cs Cf : ℕ→ℝ}
    (hs : ∀a,0≤Cs a) (hf : ∀a,0≤Cf a) (a : ℕ) :
    0≤(errorBudget R Cs Cf a).1 ∧ 0≤(errorBudget R Cs Cf a).2 := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [errorBudget]
    have h1 : 0≤∑b:Fin a,(errorBudget R Cs Cf b).1 := Finset.sum_nonneg fun b _=>(ih b b.isLt).1
    have h2 : 0≤∑b:Fin a,(errorBudget R Cs Cf b).2 := Finset.sum_nonneg fun b _=>(ih b b.isLt).2
    exact ⟨add_nonneg (hs a) h2,add_nonneg (add_nonneg (add_nonneg (hs a) h2) (mul_nonneg hR h1)) (hf a)⟩

theorem finite_graph_trace (J : Interaction n) (E F Es Ef : ℕ→Interaction n)
    (p : (a : ℕ)→Fin a→Fin n→ℝ) (r : (a : ℕ)→Fin a→ℝ)
    (hE : ∀a,E a=(∑b:Fin a,Matrix.diagonal (p a b)*F b)+Es a)
    (hF : ∀a,F a=J*E a-(∑b:Fin a,r a b • E b)+Ef a)
    {A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (hR : 0≤R) (hM : 0≤M)
    (hp : ∀a≤N,∀b i,|p a b i|≤A) (hr : ∀a≤N,∀b,|r a b|≤R)
    (hs : ∀a≤N,TraceControl (Es a) (Cs a)) (hf : ∀a≤N,TraceControl (Ef a) (Cf a))
    (hw : WordTestBound J A M L) :
    ∀a≤N,
      (∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (matrixWord J w*E a)|≤(errorBudget R Cs Cf a).1*M) ∧
      (∀w:OrdinaryWord n,w.length+2*a+2≤L→wordBounded A w→
        |trace (matrixWord J w*F a)|≤(errorBudget R Cs Cf a).2*M) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha
    have hs₀ : 0≤Cs a := (hs a ha).nonneg
    have hf₀ : 0≤Cf a := (hf a ha).nonneg
    have hprev (b : Fin a) := ih b b.isLt (b.isLt.le.trans ha)
    have hCs (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
        |trace (matrixWord J w*Es a)|≤Cs a*M := by
      apply (hs a ha).bound _ |>.trans
      simpa only [mul_comm] using mul_le_mul (hw w hlen hwb) (le_refl (Cs a)) hs₀ hM
    have hCf (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
        |trace (matrixWord J w*Ef a)|≤Cf a*M :=
      (hf a ha).bound _ |>.trans (mul_le_mul_of_nonneg_left (hw w hlen hwb) hf₀)
    have hsource : ∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (matrixWord J w*E a)|≤(errorBudget R Cs Cf a).1*M := by
      intro w hlen hwb
      have hterms (b : Fin a) : |trace (matrixWord J w*(Matrix.diagonal (p a b)*F b))|≤
          (errorBudget R Cs Cf b).2*M := by
        have H:=(hprev b).2 (w++[.diag (p a b)]) (by simp only [List.length_append,List.length_singleton]; omega)
          (wordBounded_diag hwb _ (hp a ha b))
        simpa only [matrixWord_append,matrixWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
          matrixLetter,List.map_append,List.prod_append,mul_one,mul_assoc] using H
      rw [hE a,mul_add,trace_add,errorBudget]
      dsimp only
      have H:=(Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun b:Fin a=>trace (matrixWord J w*(Matrix.diagonal (p a b)*F b)))).trans
        (Finset.sum_le_sum fun b _=>hterms b)
      rw [←trace_sum,←Matrix.mul_sum,←Finset.sum_mul] at H
      exact ((abs_add_le _ _).trans (add_le_add H (hCs w (by omega) hwb))).trans_eq (by ring)
    refine ⟨hsource,?_⟩
    intro w hlen hwb
    have hsnew:=hsource (w++[.noise]) (by simp only [List.length_append,List.length_singleton]; omega)
      (wordBounded_noise hwb)
    have Hs : |trace (matrixWord J w*(J*E a))|≤(errorBudget R Cs Cf a).1*M := by
      simpa only [matrixWord_append,matrixWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
        matrixLetter,List.map_append,List.prod_append,mul_one,mul_assoc] using hsnew
    have hterms (b : Fin a) : |trace (matrixWord J w*(r a b • E b))|≤
        R*(errorBudget R Cs Cf b).1*M := by
      have H:=(hprev b).1 w (by omega) hwb
      rw [Matrix.mul_smul,trace_smul,smul_eq_mul,abs_mul]
      exact ((mul_le_mul_of_nonneg_right (hr a ha b) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left H hR)).trans_eq (by ring)
    have H:=(Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun b:Fin a=>trace (matrixWord J w*(r a b • E b)))).trans
      (Finset.sum_le_sum fun b _=>hterms b)
    rw [←trace_sum,←Matrix.mul_sum] at H
    rw [hF a,mul_add,mul_sub,trace_add,trace_sub]
    apply ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add Hs H))
      (hCf w (by omega) hwb))).trans_eq
    rw [errorBudget]
    dsimp only
    rw [←Finset.sum_mul,←Finset.mul_sum]
    ring

end SKGapCutoff.Recipe

end
end

end OAI
