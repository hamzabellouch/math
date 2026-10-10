import Mathlib
import OAI.Probability.SKGap.Matrix.GOEDiagonalSquare
import OAI.Probability.SKGap.Matrix.GOESubmatrix

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius

theorem zeroDiagGOE_norm_tail {j : ℝ} (hj : 0<j) {n : ℕ} (hn : 0<n) :
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | 2*sqrt j+1+1<opNorm (removeDiagonal (goeMatrix (j/n) g))} ≤
      ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
      ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n)))) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  have hr : 0<j/(n:ℝ) := div_pos hj (Nat.cast_pos.mpr hn)
  let E := {g : MatrixCoordinates (Fin n)→ℝ | 2*sqrt j+1<opNorm (goeMatrix (j/n) g)}
  let V := {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,1 < |goeMatrix (j/n) g i i|}
  have hs : {g | 2*sqrt j+1+1<opNorm (removeDiagonal (goeMatrix (j/n) g))}⊆E∪V := by
    intro g hg
    by_contra hh
    have hh' : ¬2*sqrt j+1<opNorm (goeMatrix (j/n) g) ∧ ¬∃ i,1 < |goeMatrix (j/n) g i i| := by
      simpa only [Set.mem_union,E,V,Set.mem_ofPred_eq,not_or] using hh
    have hd : opNorm (Matrix.diagonal (fun i=>goeMatrix (j/n) g i i))≤1 :=
      opNorm_diagonal_le zero_le_one (fun i=>le_of_not_gt (fun hi=>hh'.2 ⟨i,hi⟩))
    have hsub := opNorm_sub (goeMatrix (j/n) g) (Matrix.diagonal (fun i=>goeMatrix (j/n) g i i))
    exact (not_lt_of_ge (hsub.trans (add_le_add (le_of_not_gt hh'.1) hd))) hg
  have he : μ E≤ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j))) := by
    rw [←ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    have ht := goe_norm_tail (ι:=Fin n) hj (show (0:ℝ)≤1 by norm_num)
    simpa only [one_pow,neg_mul,one_mul,Fintype.card_fin,matrixOperator,μ,E,opNorm] using ht
  have hv : μ V≤ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n)))) := by
    rw [←ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_pow,Fintype.card_fin] using goe_diagonal_tail (ι:=Fin n) hr (show (0:ℝ)≤1 by norm_num)
  exact ((measure_mono hs).trans (measure_union_le E V)).trans (add_le_add he hv)
end SKGap
end
end

end OAI
