import Mathlib
import OAI.Probability.SKGap.Matrix.WordDiag
import OAI.Probability.SKGap.Matrix.RecipeWordEvent

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma wordBounded_lift (A : ℝ) (w : OrdinaryWord n) :
    wordBounded A w ↔ ∀l∈liftWord w,l.bounded A := by
  constructor
  · intro h l hl
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hl
    cases a <;> exact h _ ha
  · intro h l hl
    have hh:=h (Letter.toWord l) (List.mem_map.mpr ⟨l,hl,rfl⟩)
    cases l <;> exact hh

def WordSeminormBound (J : Interaction n) (j A C : ℝ) (L : ℕ) : Prop :=
  ∀(p : Bool) (w : OrdinaryWord n),w.length≤L→wordBounded A w→
    matrixWordSeminorm p (matrixWord J w-Matrix.diagonal (Diagram.prediction j w))≤C

lemma wordSeminormBound_diagram {J : Interaction n} {j A C : ℝ} {L : ℕ}
    (h : WordSeminormBound J j A C L) : WordDiagramBound J j A C L := h false

lemma offDiagonalSeminorm_sub_diagonal (M : Interaction n) (a : Fin n→ℝ) :
    SKGap.offDiagonalSeminorm (M-Matrix.diagonal a)=SKGap.offDiagonalSeminorm M := by
  unfold SKGap.offDiagonalSeminorm
  congr 1
  ext ⟨i,k⟩
  by_cases hik:i=k <;> simp [SKGap.offDiagonalVector,Matrix.diagonal_apply,hik]

lemma matrixWord_opNorm (J : Interaction n) (hn : 0<n) {R : ℝ}
    (hR : 1≤R) (hJ : SKGap.opNorm J≤R) (w : OrdinaryWord n) (hw : wordBounded R w) :
    SKGap.opNorm (matrixWord J w)≤R^w.length := by
  let : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  induction w with
  | nil=>simpa [matrixWord] using (SKGap.opNorm_one_le (ι:=Fin n))
  | cons l w ih=>
    have hl : SKGap.opNorm (matrixLetter J l)≤R := by
      cases l with
      | noise=>exact hJ
      | diag a=>exact SKGap.opNorm_diagonal_le (by linarith) (hw (.diag a) (List.mem_cons_self))
    have hh:=ih (fun a ha=>hw a (List.mem_cons_of_mem _ ha))
    simp only [matrixWord,List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    exact (SKGap.opNorm_mul _ _).trans ((mul_le_mul hl hh (norm_nonneg _) (by linarith)).trans_eq (mul_comm _ _))

lemma wordSeminormBound_test {J : Interaction n} {j A C R : ℝ} {L : ℕ}
    (h : WordSeminormBound J j A C L) (hn : 0<n) (hR : 1≤R) (hA : A≤R) (hJ : SKGap.opNorm J≤R) :
    WordTestBound J A (R^L+C) L := by
  intro w hw hb
  have hs:=h true w hw hb
  simp only [matrixWordSeminorm,↓reduceIte,offDiagonalSeminorm_sub_diagonal] at hs
  exact add_le_add ((matrixWord_opNorm J hn hR hJ w (wordBounded_mono hb hA)).trans
    (pow_le_pow_right₀ hR hw)) hs

theorem ordinary_word_event {j A : ℝ} (hj : 0<j) (hj1 : j<1) (hA : 1≤A) (L : ℕ) :
    ∃(C : ℝ) (N : ℕ),0<C ∧ 0<N ∧ ∀n,N≤n→
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ¬WordSeminormBound (removeDiagonal (goeMatrix (j/n) g)) j A C L}≤
      2*((wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
        ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))+
        (ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
          ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n)))))) := by
  have hs : sqrt j*(1:ℝ)<1 := by nlinarith [sq_sqrt hj.le,sqrt_nonneg j]
  obtain ⟨C,N,hC,hN,hb⟩:=zeroDiag_exact_words_two_seminorms hj (by norm_num : (0:ℝ)<1)
    hs hA hA (by norm_num : (0:ℝ)<1) L
  refine ⟨C,N,hC,hN,fun n hn=>?_⟩
  apply (measure_mono ?_).trans (hb n hn)
  intro g hg
  simp only [WordSeminormBound,not_forall,not_le] at hg
  obtain ⟨p,w,hw,hwb,hfail⟩:=hg
  refine ⟨p,(fun _=>0),liftWord w,?_,?_,(wordBounded_lift A w).mp hwb,?_,?_,?_⟩
  · intro i; norm_num
  · simpa [liftWord] using hw
  · simp
  · exact Or.inl (inverseCount_lift w)
  · have he : wordPrediction j (fun _ : Fin n=>0) 1 (liftWord w)=Diagram.prediction j w:=
      funext (wordPrediction_lift j _ _ _)
    simpa only [exactWord_lift,he] using hfail

end SKGapCutoff.Recipe

end
end

end OAI
