import Mathlib
import OAI.Probability.SKGap.Localization.PrimaryQuenched
import OAI.Probability.SKGap.Stability.OrdinaryWordEvent

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma WordSeminormBound.mono {J : Interaction n} {j A C : ℝ} {L K : ℕ}
    (h : WordSeminormBound J j A C L) (hK : K≤L) : WordSeminormBound J j A C K :=
  fun p w hw hb=>h p w (hw.trans hK) hb

def primaryEventBudget (j R C : ℝ) (M : ℕ) : ℝ :=
  ∑q:Fin M,(formalOpBound j R (q.val+1)+massBound j (q.val+1)*C)
lemma primaryEventBudget_nonneg {j R C : ℝ} (hR : 0≤R) (hC : 0≤C) (M : ℕ) :
    0≤primaryEventBudget j R C M :=
  Finset.sum_nonneg (fun _ _=>add_nonneg (formalOpBound_nonneg j hR _) (mul_nonneg (massBound_pos j _).le hC))

lemma wordEvent_formal {j R A C : ℝ} (J : Interaction n) (hn : 0<n)
    (hR : 0≤R) (hC : 0≤C) (hA : 1≤A) (hJ : SKGap.opNorm J≤R) (M L : ℕ) (hML : 2*M≤L)
    (hw : WordSeminormBound J j A C L) (h : Fin n→ℝ) (x : Spin n) (l : ℕ) (hl : l<M) :
    ShapeBound (formalField j J h x l) (primaryEventBudget j R C M) := by
  let : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  let q:Fin M:=⟨l,hl⟩
  have hnon := formalOpBound_nonneg j hR (l+1)
  have hmass := mul_nonneg (massBound_pos j (l+1)).le hC
  have hb:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun q:Fin M=>formalOpBound j R (q.val+1)+massBound j (q.val+1)*C)
    (fun q _=>add_nonneg (formalOpBound_nonneg j hR _) (mul_nonneg (massBound_pos j _).le hC))
    (Finset.mem_univ q)
  have ho : formalOpBound j R (l+1)≤primaryEventBudget j R C M :=
    (le_add_of_nonneg_right hmass).trans hb
  have hm : massBound j (l+1)*C≤primaryEventBudget j R C M :=
    (le_add_of_nonneg_left hnon).trans hb
  have ha:=primaryDiagonal_bounded j J h x
  have hp (p : Bool) : matrixWordSeminorm p (formalField j J h x l)≤primaryEventBudget j R C M := by
    apply (primaryMatrix_seminorm p j J (primaryDiagonal j J h x) (l+1) (by omega) ?_).trans
    · exact (mul_le_mul_of_nonneg_right (primaryMass_bound j _ ha (l+1)) hC).trans hm
    · intro t ht
      have htB:=primaryPolynomial_admissible j _ ha (l+1) t ht
      exact hw p t.2 (htB.1.trans (by omega))
        (wordBounded_mono ((wordBounded_lift 1 _).mpr htB.2) hA)
  exact ⟨(primaryMatrix_opNorm J _ hn hR hJ ha (l+1)).trans ho,hp false,hp true⟩

def RecipeMatrixEvent (j R A B W C : ℝ) (M Nmax : ℕ) (J : Interaction n) : Prop :=
  SKGap.opNorm J≤R ∧
  (∀h x l,l<M→ShapeBound (formalField j J h x l) B) ∧
  WordTestBound J A W (2*Nmax+3) ∧ WordDiagramBound J j A C ((2*M+1)+2*Nmax+2)

lemma wordEvent_recipeEvent {j R A C : ℝ} (J : Interaction n) (hn : 0<n)
    (hR : 1≤R) (hA : 1≤A) (hAR : A≤R) (hC : 0≤C) (hJ : SKGap.opNorm J≤R)
    (M Nmax : ℕ) (hw : WordSeminormBound J j A C (2*M+2*Nmax+3)) :
    RecipeMatrixEvent j R A (primaryEventBudget j R C M) (R^(2*Nmax+3)+C) C M Nmax J := by
  refine ⟨hJ,fun h x l hl=>wordEvent_formal J hn (by linarith) hC hA hJ M _ (by omega) hw h x l hl,
    wordSeminormBound_test (hw.mono (by omega)) hn hR hAR hJ,?_⟩
  exact wordSeminormBound_diagram (hw.mono (by omega))

end SKGapCutoff.Recipe

end
end

end OAI
