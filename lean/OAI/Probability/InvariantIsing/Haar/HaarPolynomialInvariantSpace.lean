import OAI.Probability.InvariantIsing.Haar.HaarPolynomialSpace
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialLaplacian

namespace OAI

/-! The finite polynomial spaces are invariant under every rotation derivative. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialDerivation_word_mem {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (d : ℕ)
    (w : Fin d → Option (Fin N × Fin N)) :
    matrixPolynomialDerivation A (haarPolynomialWord w) ∈ haarPolynomialSpace N d := by
  induction d with
  | zero =>
    simp [haarPolynomialWord]
  | succ d ih =>
    rw [← Fin.cons_self_tail w,haarPolynomialWord_cons,Derivation.leibniz]
    simp only [smul_eq_mul]
    apply (haarPolynomialSpace N (d+1)).add_mem
    · exact haarPolynomialSpace_atom_mul (w 0) (ih (Fin.tail w))
    · cases h : w 0 with
      | none => simp [haarPolynomialAtom]
      | some ij =>
        rcases ij with ⟨i,j⟩
        simp only [haarPolynomialAtom,matrixPolynomialDerivation_X,Finset.mul_sum]
        apply (haarPolynomialSpace N (d+1)).sum_mem
        intro k _
        rw [mul_smul_comm]
        apply (haarPolynomialSpace N (d+1)).smul_mem
        simpa only [haarPolynomialAtom,mul_comm] using
          haarPolynomialSpace_atom_mul (some (k,j)) (haarPolynomialWord_mem (Fin.tail w))

lemma haarPolynomialDerivation_mem {N d : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) {p : MatrixPolynomial N}
    (hp : p ∈ haarPolynomialSpace N d) :
    matrixPolynomialDerivation A p ∈ haarPolynomialSpace N d := by
  refine Submodule.span_induction (p := fun q _ =>
    matrixPolynomialDerivation A q ∈ haarPolynomialSpace N d) ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with ⟨w,rfl⟩
    exact haarPolynomialDerivation_word_mem A d w
  · simpa only [map_zero] using (haarPolynomialSpace N d).zero_mem
  · intro p q _ _ hp hq
    rw [map_add]
    exact (haarPolynomialSpace N d).add_mem hp hq
  · intro c p _ hp
    rw [Derivation.map_smul]
    exact (haarPolynomialSpace N d).smul_mem c hp

lemma haarPolynomialLaplacian_mem {N d : ℕ} {p : MatrixPolynomial N}
    (hp : p ∈ haarPolynomialSpace N d) :
    haarPolynomialLaplacian N p ∈ haarPolynomialSpace N d := by
  rw [haarPolynomialLaplacian_apply]
  apply (haarPolynomialSpace N d).sum_mem
  intro i _
  apply (haarPolynomialSpace N d).sum_mem
  intro j _
  exact haarPolynomialDerivation_mem _ (haarPolynomialDerivation_mem _ hp)

end InvariantIsing

end

end OAI
