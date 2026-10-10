import Mathlib
import OAI.Probability.SKGap.Matrix.PrimitiveTrace
import OAI.Probability.SKGap.Matrix.ClosedTrace

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

theorem finite_graph_trace_tested (J : Interaction n) (E F Es Ef : ℕ→Interaction n)
    (p : (a : ℕ)→Fin a→Fin n→ℝ) (r : (a : ℕ)→Fin a→ℝ)
    (hE : ∀a,E a=(∑b:Fin a,Matrix.diagonal (p a b)*F b)+Es a)
    (hF : ∀a,F a=J*E a-(∑b:Fin a,r a b • E b)+Ef a)
    {A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (_ : 0≤R) (_ : 0≤M)
    (hp : ∀a≤N,∀b i,|p a b i|≤A) (hr : ∀a≤N,∀b,|r a b|≤R)
    (hsn : ∀a≤N,0≤Cs a) (hfn : ∀a≤N,0≤Cf a)
    (hs : ∀a≤N,∀w:OrdinaryWord n,w.length≤L→wordBounded A w→
      |trace (matrixWord J w*Es a)|≤Cs a*M)
    (hf : ∀a≤N,∀w:OrdinaryWord n,w.length≤L→wordBounded A w→
      |trace (matrixWord J w*Ef a)|≤Cf a*M) :
    ∀a≤N,
      (∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (matrixWord J w*E a)|≤(errorBudget R Cs Cf a).1*M) ∧
      (∀w:OrdinaryWord n,w.length+2*a+2≤L→wordBounded A w→
        |trace (matrixWord J w*F a)|≤(errorBudget R Cs Cf a).2*M) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha
    have hs₀ : 0≤Cs a := hsn a ha
    have hf₀ : 0≤Cf a := hfn a ha
    have hprev (b : Fin a) := ih b b.isLt (b.isLt.le.trans ha)
    have hCs (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
        |trace (matrixWord J w*Es a)|≤Cs a*M :=
      hs a ha w hlen hwb
    have hCf (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
        |trace (matrixWord J w*Ef a)|≤Cf a*M :=
      hf a ha w hlen hwb
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
      have hB : 0≤(errorBudget R Cs Cf b).1*M := (abs_nonneg _).trans H
      rw [Matrix.mul_smul,trace_smul,smul_eq_mul,abs_mul]
      exact ((mul_le_mul_of_nonneg_left H (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hr a ha b) hB)).trans_eq (by ring)
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

def closedWordBounded (A : ℝ) (w : List (WordLetter (Fin n))) : Prop :=
  ∀l∈w,match l with | .diag p=>∀i,|p i|≤A | .noise=>True | .inverse=>True

def ClosedWordTestBound (j : ℝ) (a : Fin n→ℝ) (J : Interaction n)
    (A M : ℝ) (L : ℕ) : Prop :=
  ∀w:List (WordLetter (Fin n)),w.length≤L→inverseCount w≤1→closedWordBounded A w→
    testSize (exactWord j a w J)≤M

lemma closedWordBounded_append {A : ℝ} {P Q : List (WordLetter (Fin n))}
    (hP : closedWordBounded A P) (hQ : closedWordBounded A Q) : closedWordBounded A (P++Q) := by
  intro l hl;rcases List.mem_append.mp hl with hl|hl
  · exact hP l hl
  · exact hQ l hl
lemma closedWordBounded_lift {A : ℝ} {w : OrdinaryWord n} (hw : wordBounded A w) :
    closedWordBounded A (liftWord w) := by
  intro l hl
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hl
  cases q with
  | diag p=>exact hw _ hq
  | noise=>trivial

lemma implicit_error_elimination (A J K E F Es Ef : Interaction n) (q : ℝ)
    (hK : K*(1-A*(J-q • 1))=1)
    (hE : E=A*F+Es) (hF : F=(J-q • 1)*E+Ef) :
    E=K*(Es+A*Ef) := by
  have he : (1-A*(J-q • 1))*E=Es+A*Ef := by
    rw [sub_mul,one_mul,mul_assoc]
    rw [hF,mul_add] at hE
    nth_rw 1 [hE]
    abel
  have hk:=congrArg (fun P:Interaction n=>K*P) he
  rw [←mul_assoc,hK,one_mul] at hk
  exact hk

theorem implicit_trace_bound (j : ℝ) (a : Fin n→ℝ) (J Es Ef : Interaction n)
    {C D A M : ℝ} {L : ℕ} (hs : TraceControl Es C) (hf : TraceControl Ef D)
    (ha : ∀i,|a i|≤A) (hw : ClosedWordTestBound j a J A M L)
    (w : OrdinaryWord n) (hlen : w.length+2≤L) (hwb : wordBounded A w) :
    |trace (matrixWord J w*((WordLetter.inverse.exactEval j a J)*(Es+Matrix.diagonal a*Ef)))|
      ≤(C+D)*M := by
  have hb₁ : closedWordBounded (n:=n) A [WordLetter.inverse] := by
    intro l hl;have hl₀:=List.mem_singleton.mp hl;subst l;trivial
  have hb₂ : closedWordBounded A [WordLetter.inverse,.diag a] := by
    intro l hl;simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · trivial
    · exact ha
  have h₁ := hw (liftWord w++[.inverse])
    (by simpa only [liftWord,List.length_map,List.length_append,List.length_singleton] using (show w.length+1≤L by omega))
    (by rw [inverseCount_append,inverseCount_lift];simp [inverseCount]) (closedWordBounded_append (closedWordBounded_lift hwb) hb₁)
  have h₂ := hw (liftWord w++[.inverse,.diag a])
    (by simpa only [liftWord,List.length_map,List.length_append,List.length_cons,List.length_nil] using hlen)
    (by rw [inverseCount_append,inverseCount_lift];simp [inverseCount]) (closedWordBounded_append (closedWordBounded_lift hwb) hb₂)
  rw [exactWord_append,exactWord_lift] at h₁ h₂
  simp only [exactWord,matrixFactorProduct,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one,WordLetter.exactEval] at h₁ h₂
  have H₁:=(hs.bound (matrixWord J w*WordLetter.inverse.exactEval j a J)).trans
    (mul_le_mul_of_nonneg_left h₁ hs.nonneg)
  have H₂:=(hf.bound (matrixWord J w*WordLetter.inverse.exactEval j a J*Matrix.diagonal a)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [mul_assoc,WordLetter.exactEval] using h₂) hf.nonneg)
  rw [mul_add,mul_add,trace_add]
  exact ((abs_add_le _ _).trans (add_le_add
    (by simpa only [mul_assoc] using H₁) (by simpa only [mul_assoc] using H₂))).trans_eq (by ring)

theorem implicit_source_field_trace (j : ℝ) (a : Fin n→ℝ) (J E F Es Ef : Interaction n) (q : ℝ)
    (hE : E=WordLetter.inverse.exactEval j a J*(Es+Matrix.diagonal a*Ef))
    (hF : F=(J-q • 1)*E+Ef)
    {C D A M : ℝ} {L : ℕ} (hs : TraceControl Es C) (hf : TraceControl Ef D)
    (ha : ∀i,|a i|≤A) (hw : ClosedWordTestBound j a J A M L)
    (w : OrdinaryWord n) (hlen : w.length+3≤L) (hwb : wordBounded A w) :
    |trace (matrixWord J w*E)|≤(C+D)*M ∧
    |trace (matrixWord J w*F)|≤((1+|q|)*(C+D)+D)*M := by
  have HE : |trace (matrixWord J w*E)|≤(C+D)*M := by
    rw [hE];exact implicit_trace_bound j a J Es Ef hs hf ha hw w (by omega) hwb
  have HJ : |trace (matrixWord J w*(J*E))|≤(C+D)*M := by
    have H:=implicit_trace_bound j a J Es Ef hs hf ha hw (w++[.noise])
      (by simp only [List.length_append,List.length_singleton];omega) (wordBounded_noise hwb)
    simpa only [←hE,matrixWord_append,matrixWord,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,List.map_append,List.prod_append,matrixLetter,mul_one,mul_assoc] using H
  have Hf : |trace (matrixWord J w*Ef)|≤D*M := by
    have H:=hw (liftWord w) (by simp only [liftWord,List.length_map];omega)
      (by simp) (closedWordBounded_lift hwb)
    rw [exactWord_lift] at H
    exact (hf.bound _).trans (mul_le_mul_of_nonneg_left H hf.nonneg)
  refine ⟨HE,?_⟩
  rw [hF,sub_mul,smul_mul_assoc,one_mul,mul_add,mul_sub,Matrix.mul_smul,
    trace_add,trace_sub,trace_smul,smul_eq_mul]
  have HQ : |q*trace (matrixWord J w*E)|≤|q| *((C+D)*M) := by
    rw [abs_mul];exact mul_le_mul_of_nonneg_left HE (abs_nonneg _)
  exact ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add HJ HQ)) Hf)).trans_eq (by ring)

lemma ClosedWordTestBound.ordinary {j : ℝ} {a : Fin n→ℝ} {J : Interaction n}
    {A M : ℝ} {L : ℕ} (h : ClosedWordTestBound j a J A M L) : WordTestBound J A M L := by
  intro w hw hb
  have H:=h (liftWord w) (by simpa only [liftWord,List.length_map] using hw)
    (by simp) (closedWordBounded_lift hb)
  simpa only [exactWord_lift] using H

theorem closed_finite_graph_trace (j : ℝ) (a₀ : Fin n→ℝ) (J : Interaction n)
    (E F Es Ef : ℕ→Interaction n) (P Q : Interaction n) (q : ℝ)
    (p : (a : ℕ)→Fin a→Fin n→ℝ) (r : (a : ℕ)→Fin a→ℝ)
    (hE : ∀a,E a=(∑b:Fin a,Matrix.diagonal (p a b)*F b)+Es a)
    (hF : ∀a,F a=J*E a-(∑b:Fin a,r a b • E b)+Ef a)
    (hEs : Es 0=WordLetter.inverse.exactEval j a₀ J*(P+Matrix.diagonal a₀*Q))
    (hEf : Ef 0=(-q) • Es 0+Q)
    {C D A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (hP : TraceControl P C) (hQ : TraceControl Q D)
    (hR : 0≤R) (hM : 0≤M) (ha : ∀i,|a₀ i|≤A)
    (hp : ∀a≤N,∀b i,|p a b i|≤A) (hr : ∀a≤N,∀b,|r a b|≤R)
    (hs : ∀a≤N,0<a→TraceControl (Es a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (Ef a) (Cf a))
    (hw : ClosedWordTestBound j a₀ J A M (L+2)) :
    let Bs:=fun a=>if a=0 then C+D else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+D)+D else Cf a
    ∀a≤N,
      (∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (matrixWord J w*E a)|≤(errorBudget R Bs Bf a).1*M) ∧
      (∀w:OrdinaryWord n,w.length+2*a+2≤L→wordBounded A w→
        |trace (matrixWord J w*F a)|≤(errorBudget R Bs Bf a).2*M) := by
  dsimp only
  have hsource (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
      |trace (matrixWord J w*Es 0)|≤(C+D)*M := by
    rw [hEs]
    exact implicit_trace_bound j a₀ J P Q hP hQ ha hw w (by omega) hwb
  have hfield (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
      |trace (matrixWord J w*Ef 0)|≤(|q| *(C+D)+D)*M := by
    have H₁:=hsource w hlen hwb
    have H₂:=(hQ.bound (matrixWord J w)).trans (mul_le_mul_of_nonneg_left
      (hw.ordinary w (by omega) hwb) hQ.nonneg)
    rw [hEf,mul_add,Matrix.mul_smul,trace_add,trace_smul,smul_eq_mul]
    have H₃ : |(-q)*trace (matrixWord J w*Es 0)|≤|q| *((C+D)*M) := by
      rw [abs_mul,abs_neg];exact mul_le_mul_of_nonneg_left H₁ (abs_nonneg q)
    exact ((abs_add_le _ _).trans (add_le_add H₃ H₂)).trans_eq (by ring)
  apply finite_graph_trace_tested J E F Es Ef p r hE hF hR hM hp hr
  · intro a haN;split_ifs with h
    · exact add_nonneg hP.nonneg hQ.nonneg
    · exact (hs a haN (Nat.pos_of_ne_zero h)).nonneg
  · intro a haN;split_ifs with h
    · exact add_nonneg (mul_nonneg (abs_nonneg _) (add_nonneg hP.nonneg hQ.nonneg)) hQ.nonneg
    · exact (hf a haN (Nat.pos_of_ne_zero h)).nonneg
  · intro a haN w hlen hwb
    by_cases ha0 : a=0
    · subst a;simpa only [ite_true] using hsource w hlen hwb
    · simpa only [ite_eq_right ha0] using (hs a haN (Nat.pos_of_ne_zero ha0)).bound (matrixWord J w) |>.trans
        (mul_le_mul_of_nonneg_left (hw.ordinary w (by omega) hwb) (hs a haN (Nat.pos_of_ne_zero ha0)).nonneg)
  · intro a haN w hlen hwb
    by_cases ha0 : a=0
    · subst a;simpa only [ite_true] using hfield w hlen hwb
    · simpa only [ite_eq_right ha0] using (hf a haN (Nat.pos_of_ne_zero ha0)).bound (matrixWord J w) |>.trans
        (mul_le_mul_of_nonneg_left (hw.ordinary w (by omega) hwb) (hf a haN (Nat.pos_of_ne_zero ha0)).nonneg)

end SKGapCutoff.Recipe

end
end

end OAI
