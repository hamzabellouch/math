import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceBasis

namespace OAI

/-! The nearest-neighbor reference chain has only two zero-wall sectors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaReferenceWalls (n : ℕ) (s : SourceSpinBasis (n+1)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => s i.castSucc ≠ s i.succ)).card

theorem qmaReferenceWalls_zero_iff (n : ℕ) (s : SourceSpinBasis (n+1)) :
    qmaReferenceWalls n s = 0 ↔ ∀ i, s i = s 0 := by
  constructor
  · intro h
    have he : Finset.univ.filter (fun i : Fin n => s i.castSucc ≠ s i.succ) = ∅ :=
      Finset.card_eq_zero.mp h
    have hadj (i : Fin n) : s i.castSucc = s i.succ := by
      by_contra hn
      have hm : i ∈ Finset.univ.filter (fun i : Fin n => s i.castSucc ≠ s i.succ) := by
        simp [hn]
      rw [he] at hm
      exact Finset.notMem_empty i hm
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hadj i).symm.trans ih
  · intro h
    unfold qmaReferenceWalls
    have he : Finset.univ.filter (fun i : Fin n => s i.castSucc ≠ s i.succ) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ hn
      exact hn ((h i.castSucc).trans (h i.succ).symm)
    rw [he]
    rfl

theorem qmaReferenceWalls_constant (n : ℕ) (b : Fin 2) :
    qmaReferenceWalls n (fun _ => b) = 0 :=
  (qmaReferenceWalls_zero_iff n _).mpr (by intro i; rfl)

theorem qmaReferenceWalls_pos (n : ℕ) (s : SourceSpinBasis (n+1))
    (hs : ¬∀ i, s i = s 0) : 1 ≤ qmaReferenceWalls n s := by
  have hn : qmaReferenceWalls n s ≠ 0 := fun h => hs ((qmaReferenceWalls_zero_iff n s).mp h)
  omega

def qmaReferenceWallMatrix (n : ℕ) :
    Matrix (SourceSpinBasis (n+1)) (SourceSpinBasis (n+1)) ℂ :=
  Matrix.diagonal (fun s => (qmaReferenceWalls n s : ℂ))

theorem qmaReferenceWallMatrix_quadratic (n : ℕ) (u : SourceSpinBasis (n+1) → ℂ) :
    qmaQuadratic (qmaReferenceWallMatrix n) u =
      ∑ s, (qmaReferenceWalls n s : ℝ)*Complex.normSq (u s) := by
  simp only [qmaQuadratic,qmaReferenceWallMatrix,Matrix.mulVec_diagonal,dotProduct,
    Pi.star_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp [Complex.mul_re,Complex.normSq_apply]
  ring

theorem qmaReferenceWallMatrix_gap (n : ℕ) (u : SourceSpinBasis (n+1) → ℂ) :
    (∑ s, if ∀ i, s i = s 0 then 0 else Complex.normSq (u s)) ≤
      qmaQuadratic (qmaReferenceWallMatrix n) u := by
  rw [qmaReferenceWallMatrix_quadratic]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : ∀ i, s i = s 0
  · simp [hs,(qmaReferenceWalls_zero_iff n s).mpr hs]
  · simp only [hs,ite_false]
    have h : (1 : ℝ) ≤ qmaReferenceWalls n s := by
      exact_mod_cast qmaReferenceWalls_pos n s hs
    nlinarith [Complex.normSq_nonneg (u s)]

end ContinuumCoulomb

end

end OAI
