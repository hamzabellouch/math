import OAI.Analysis.Pureness.States.FiniteFamilyNuclearTrace
import OAI.Analysis.Pureness.Cuntz.MatrixTraceCorrespondence

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace ComplexQuasitrace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (T : ComplexQuasitrace (CStarMatrix ι ι A))
variable (hadd : ∀ X Y, T (X+Y)=T X+T Y)

include hadd in
lemma matrix_diagonal_eq_of_additive (i j : ι) (a : A) :
    T (singleMatrix i i a)=T (singleMatrix j j a) := by
  let L := T.additiveLinear hadd
  have hcyc := linearMap_tracial_of_star_mul L (by
    intro X
    simp only [L,additiveLinear_apply]
    exact T.polar X)
  have h := hcyc (singleMatrix i j a) (singleMatrix j i 1)
  simpa only [singleMatrix_mul_same,mul_one,one_mul,L,additiveLinear_apply] using h

include hadd in
lemma matrix_eq_sum_diagonal_of_additive (M : CStarMatrix ι ι A) :
    T M=∑ i, T (singleMatrix i i (M i i)) := by
  let L := T.additiveLinear hadd
  have hcyc := linearMap_tracial_of_star_mul L (by
    intro X
    simp only [L,additiveLinear_apply]
    exact T.polar X)
  have hoff (i j : ι) (hij : i ≠ j) (a : A) : L (singleMatrix i j a)=0 := by
    have h := hcyc (singleMatrix i i 1) (singleMatrix i j a)
    rw [singleMatrix_mul_same,one_mul,singleMatrix_mul_ne i j i i hij.symm,_root_.map_zero] at h
    exact h
  suffices h : L M=∑ i, L (singleMatrix i i (M i i)) by
    simpa only [L,additiveLinear_apply] using h
  nth_rw 1 [matrix_eq_sum_single M]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact hoff i j hji.symm (M i j)
  · simp
end ComplexQuasitrace

namespace CompatibleFiniteQuasitrace
variable (F : CompatibleFiniteQuasitrace A)

theorem level_eq_matrixTrace_of_additive (τ : TracialState A)
    (hτ : ∀ a, τ.functional a=F.toTwoQuasitrace.base a)
    (n : ℕ) (hadd : ∀ M N, F.level n (M+N)=F.level n M+F.level n N)
    (M : FinMatrix A n) : F.level n M=matrixTrace τ M := by
  cases n with
  | zero =>
    have he : M=0 := by ext i; exact Fin.elim0 i
    rw [he,(F.level 0).map_zero,_root_.map_zero]
  | succ n =>
    rw [(F.level (n+1)).matrix_eq_sum_diagonal_of_additive hadd M]
    change (∑ i, F.level (n+1) (singleMatrix i i (M i i)))=∑ i, τ.functional (M i i)
    apply Finset.sum_congr rfl
    intro i _
    rw [(F.level (n+1)).matrix_diagonal_eq_of_additive hadd i 0 (M i i),hτ]
    change F.level (n+1) (matrixCorner (0 : Fin (n+1)) (M i i))=F.level 1 (scalarMatrixHom (M i i))
    rw [← matrixInclusion_scalar_one n,F.inclusion]

end CompatibleFiniteQuasitrace
end CuntzPureness

end

end OAI
