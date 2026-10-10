import OAI.Analysis.Quantum.PPTSquare.EigenRows
import OAI.Analysis.Quantum.PPTSquare.MatrixSelection

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Matrix
namespace EigenGalois
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

lemma row_covariant (A S : Matrix ι ι K) (r : ι → K) (hr : Function.Injective r)
    (hS : IsUnit S) (he : S * A = diagonal r * S) (z : ι) (hz : ∀ i, S i z = 1)
    (σ : K ≃+* K) (hA : A.map σ.toRingHom = A)
    (π : Equiv.Perm ι) (hrσ : ∀ i, σ (r i) = r (π i)) :
    ∀ i j, σ (S i j) = S (π i) j := by
  intro i
  have hv : S.row i ᵥ* A = r i • S.row i := by
    ext j
    have hh := congrFun (congrFun he i) j
    rw [Matrix.diagonal_mul] at hh
    simpa only [Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Pi.smul_apply, smul_eq_mul, Matrix.row_apply] using hh
  have hw : (fun j => σ (S i j)) ᵥ* A = r (π i) • (fun j => σ (S i j)) := by
    ext j
    have hh := (σ.toRingHom.map_vecMul A (S.row i) j).symm
    rw [hA, hv] at hh
    simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.row_apply] at hh
    change ((fun x => σ (S i x)) ᵥ* A) j = σ (r i) * σ (S i j) at hh
    rw [hrσ] at hh
    exact hh
  have hwz : σ (S i z) = 1 := by rw [hz, map_one]
  have hh := EigenRows.normalized_row_unique S A r hr hS he z hz (π i) _ hw hwz
  intro j
  exact congrFun hh j

lemma all_minors (A S : Matrix ι ι K) (r : ι → K) (hr : Function.Injective r)
    (hS : IsUnit S) (he : S * A = diagonal r * S) (z : ι) (hz : ∀ i, S i z = 1)
    (ha : ∀ π : Equiv.Perm ι, ∃ σ : K ≃+* K, A.map σ.toRingHom = A ∧ ∀ i, σ (r i) = r (π i))
    {k : ℕ} (c : Fin k → ι) (hcol : Function.Injective c) :
    ∀ j : Fin k → ι, Function.Injective j → IsUnit (S.submatrix j c) := by
  have hi := Matrix.linearIndependent_cols_iff_isUnit.mpr hS
  have hh : LinearIndependent K (S.submatrix id c).transpose.row := hi.comp c hcol
  have hRank : (S.submatrix id c).rank = k := by
    simpa only [Matrix.rank_transpose, Fintype.card_fin] using hh.rank_matrix
  have hg : ∀ π : Equiv.Perm ι, ∃ σ : K ≃+* K,
      ∀ i j, σ ((S.submatrix id c) i j) = (S.submatrix id c) (π i) j := by
    intro π
    obtain ⟨σ,hA,hrσ⟩ := ha π
    exact ⟨σ, fun i j => row_covariant A S r hr hS he z hz σ hA π hrσ i (c j)⟩
  intro j hj
  simpa only [Matrix.submatrix_submatrix, Function.comp_def, id_eq] using
    MatrixSelection.all_row_minors_units (S.submatrix id c) hRank hg j hj

end EigenGalois

end

end OAI
