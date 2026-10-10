import Mathlib
import OAI.Probability.SKGap.Localization.MarkedDiagnostic

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ}
def PolynomialControl (A : ℝ) (L : ℕ) (P : WordPolynomial (ι:=Fin n)) : Prop :=
  ∀t∈P,wordBounded A t.2 ∧ t.2.length≤L
lemma PolynomialControl.mono {A : ℝ} {L K : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (hLK : L≤K) : PolynomialControl A K P :=
  fun t ht=>⟨(h t ht).1,(h t ht).2.trans hLK⟩
lemma PolynomialControl.append {A : ℝ} {L : ℕ} {P Q : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (hQ : PolynomialControl A L Q) : PolynomialControl A L (P++Q) := by
  intro t ht; rcases List.mem_append.mp ht with ht|ht
  · exact h t ht
  · exact hQ t ht
lemma PolynomialControl.prepend {A : ℝ} {L : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (w : OrdinaryWord n) (hw : wordBounded A w) :
    PolynomialControl A (w.length+L) (prependWords w P) := by
  intro t ht
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact ⟨wordBounded_append hw (h r hr).1,by simpa only [List.length_append] using Nat.add_le_add_left (h r hr).2 w.length⟩
lemma PolynomialControl.scale {A : ℝ} {L : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (c : ℝ) : PolynomialControl A L (SKGap.Noncrossing.Primary.scale c P) := by
  intro t ht
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact h r hr
lemma polynomialControl_nil (c : ℝ) (A : ℝ) (L : ℕ) :
    PolynomialControl (n:=n) A L [(c,[])] := by
  intro t ht
  have he:=List.mem_singleton.mp ht; subst t
  exact ⟨by intro l hl; simp at hl,Nat.zero_le _⟩
lemma polynomialControl_noise (c : ℝ) (A : ℝ) (L : ℕ) (hL : 1≤L) :
    PolynomialControl (n:=n) A L [(c,[.noise])] := by
  intro t ht
  have he:=List.mem_singleton.mp ht; subst t
  constructor
  · intro l hl
    have he:=List.mem_singleton.mp hl; subst l; trivial
  · exact hL
end SKGapCutoff.Recipe
namespace SKGapCutoff.Primary
open Recipe SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ}
theorem primaryTree_control (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ)
    {A : ℝ} (hA : 1≤A) :
    PolynomialControl A (2*k+1) ((primaryTree j J h x k).words j).1 ∧
    PolynomialControl A (2*k+1) ((primaryTree j J h x k).words j).2 := by
  induction k with
  | zero=>exact ⟨polynomialControl_nil _ _ _,polynomialControl_noise _ _ _ (by omega)⟩
  | succ k ih=>
    have hd : wordBounded A [.diag (primaryDiagonal j J h x k)] := by
      intro l hl
      have he:=List.mem_singleton.mp hl; subst l
      exact fun i=>(primaryDiagonal_bounded j J h x k i).trans hA
    have hv : PolynomialControl A (2*(k+1)+1) (prependWords [.diag (primaryDiagonal j J h x k)]
        ((primaryTree j J h x k).words j).2) :=
      (ih.2.prepend _ hd).mono (by simp only [List.length_singleton]; omega)
    have hn : wordBounded (n:=n) A [.noise] := by
      intro l hl; have he:=List.mem_singleton.mp hl; subst l; trivial
    have hh : PolynomialControl A (2*(k+1)+1) (prependWords [.noise,.diag (primaryDiagonal j J h x k)]
        ((primaryTree j J h x k).words j).2) := by
      exact (ih.2.prepend _ (wordBounded_append hn hd)).mono (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    simp only [primaryTree,SourceTree.words]
    exact ⟨hv.append (polynomialControl_nil _ _ _),
      (hh.append ((ih.1.scale _).mono (by omega))).append (polynomialControl_noise _ _ _ (by omega))⟩
end SKGapCutoff.Primary

end
end

end OAI
