import Mathlib
import OAI.Analysis.WeakInfiniteness.CuntzCopies
import OAI.Analysis.WeakInfiniteness.MatrixCutToolkit
import OAI.Analysis.WeakInfiniteness.RectangularComparison

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology ComplexOrder

open Filter

universe u

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

local instance nonunitalGramMatrixRealModule : Module ℝ (CStarMatrix (Fin n) (Fin n) A) :=
  Module.complexToReal _

omit [PartialOrder A] [StarOrderedRing A] in
def finiteGram (v : Fin n → A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (fun i j => star (v i)*v j)

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteGram_apply (v : Fin n → A) (i j : Fin n) :
    finiteGram v i j=star (v i)*v j := rfl

lemma matrix_diagonal_mul_tendsto_nonunital (X : CStarMatrix (Fin n) (Fin n) A) :
    Tendsto (fun e => diagonalCopies n e*X)
      (CStarAlgebra.approximateUnit A) (𝓝 X) := by
  have he : (fun e => diagonalCopies n e*X)=
      fun e => CStarMatrix.ofMatrix (fun i j => e*X i j) := by
    funext e
    ext i j
    change (Matrix.diagonal (fun _ : Fin n => e)*(CStarMatrix.ofMatrix.symm X)) i j=e*X i j
    rw [Matrix.diagonal_mul]
    rfl
  rw [he]
  change Tendsto (fun e => fun i j => e*X i j) _ (𝓝 (fun i j => X i j))
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
    (CStarAlgebra.increasingApproximateUnit A).tendsto_mul_right (X i j)

lemma nonunital_positive_matrix_gram_approximation
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    (M : CStarMatrix (Fin n) (Fin n) A) (hM : 0≤M)
    (ε : ℝ) (hε : 0<ε) :
    ∃ v : Fin n → A,‖finiteGram v-M‖<ε := by
  let X := CFC.sqrt M
  have hX : star X*X=M := by
    rw [show star X=X from (CFC.sqrt_nonneg M).star_eq]
    exact CFC.sqrt_mul_sqrt_self M hM
  let l := CStarAlgebra.approximateUnit A
  let hl := CStarAlgebra.increasingApproximateUnit A
  let : l.NeBot := hl.toIsApproximateUnit.neBot
  have ht := matrix_diagonal_mul_tendsto_nonunital X
  have ht' : Tendsto (fun e => star (diagonalCopies n e*X)*(diagonalCopies n e*X)) l (𝓝 M) := by
    simpa only [hX] using ht.star.mul ht
  have hev : ∀ᶠ e in l,‖star (diagonalCopies n e*X)*(diagonalCopies n e*X)-M‖<ε/2 := by
    exact (Metric.tendsto_nhds.mp ht' (ε/2) (by positivity)).mono fun e he => by
      simpa only [dist_eq_norm] using he
  obtain ⟨e,he⟩ := hev.exists
  let h := star e*e
  have hp := (hpi h (star_mul_self_nonneg e)).diagonal_absorbs (by omega : 1≤1) n
  have hc := hp.sandwich_left X
  obtain ⟨R,hR⟩ := hc (ε/2) (by positivity)
  let v : Fin n → A := fun i => e*R 0 i
  have hv : finiteGram v=R.conjTranspose*diagonalCopies 1 h*R := by
    ext i j
    change star (e*R 0 i)*(e*R 0 j)=
      ∑ k : Fin 1,(∑ l : Fin 1,star (R l i)*(diagonalCopies 1 h) l k)*R k j
    simp only [Fin.sum_univ_one,diagonalCopies,CStarMatrix.ofMatrix_apply,
      Matrix.diagonal_apply_eq,star_mul,h,mul_assoc]
  have hdiag : star (diagonalCopies n e)*diagonalCopies n e=diagonalCopies n h := by
    change star (diagonalHom n e)*diagonalHom n e=diagonalHom n (star e*e)
    rw [← map_star,← map_mul]
  have hmiddle : X.conjTranspose*diagonalCopies n h*X=
      star (diagonalCopies n e*X)*(diagonalCopies n e*X) := by
    rw [star_mul]
    rw [← hdiag]
    simp only [CStarMatrix.star_eq_conjTranspose,mul_assoc]
  refine ⟨v,?_⟩
  rw [hv]
  calc
    _ ≤ ‖R.conjTranspose*diagonalCopies 1 h*R-(X.conjTranspose*diagonalCopies n h*X)‖+
        ‖(X.conjTranspose*diagonalCopies n h*X)-M‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε/2+ε/2 := add_lt_add hR (by simpa only [hmiddle] using he)
    _ = ε := by ring

end

end

end WeakPureInfiniteness
end

end OAI
