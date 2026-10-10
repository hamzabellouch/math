import Mathlib
import OAI.Probability.SKGap.Matrix.RecipeTraceBudget

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}
lemma mass_append (P Q : WordPolynomial (ι:=Fin n)) : mass (P++Q)=mass P+mass Q := by
  simp [mass]
lemma mass_prefix (F : List (Letter (Fin n→ℝ))) (P : WordPolynomial (ι:=Fin n)) :
    mass (prependWords F P)=mass P := by simp [mass,prependWords,List.map_map,Function.comp_def]
lemma mass_scale (c : ℝ) (P : WordPolynomial (ι:=Fin n)) : mass (Primary.scale c P)=|c| *mass P := by
  induction P with
  | nil => simp [mass,Primary.scale]
  | cons t P ih =>
    simp only [Primary.scale,List.map_cons,mass,List.sum_cons,abs_mul] at *
    rw [ih]; ring
end SKGap.Noncrossing.Primary.MarkedPolynomial
namespace SKGapCutoff.Primary
open SKGap.Noncrossing.Primary MarkedPolynomial
variable {n : ℕ}

lemma primaryTree_mass (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    mass ((primaryTree j J h x k).words j).1≤(2+|j|)^k ∧
    mass ((primaryTree j J h x k).words j).2≤(2+|j|)^k := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  induction k with
  | zero => simp [primaryTree,SourceTree.words,mass]
  | succ k ih =>
    have hm := mean_abs_le_one (primaryDiagonal_bounded j J h x k)
    have hc : 0≤(2+|j|)^k := by positivity
    have hj : 0≤|j| := abs_nonneg _
    have ht : |j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)|≤|j| := by
      rw [abs_mul]; simpa using mul_le_mul_of_nonneg_left hm hj
    simp only [primaryTree,SourceTree.words,mass_append,mass_prefix,mass_scale]
    have hz₁ : mass ([(0,[])] : WordPolynomial (ι:=Fin n))=0 := by simp [mass]
    have hz₂ : mass ([(0,[.noise])] : WordPolynomial (ι:=Fin n))=0 := by simp [mass]
    simp only [hz₁,hz₂,add_zero,abs_neg]
    constructor
    · rw [pow_succ]; nlinarith [ih.2,mul_nonneg hj hc]
    · have ht' := mul_le_mul ht ih.1 (mass_nonneg _) hj
      rw [pow_succ]
      nlinarith [ih.2]

end SKGapCutoff.Primary

end
end

end OAI
