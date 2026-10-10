import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootGlobalCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.BilateralNeutralLifts

namespace OAI

/-! # Diagonal and unipotent coordinates of a weak stable displacement -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Positive upper triangular matrices split into a positive diagonal
matrix and an actual ordered upper-root word. -/
theorem upper_triangular_positive_diagonal_factorization {n : ℕ} (g : G n)
    (htri : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i) :
    ∃ (v : Fin n → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime n),
      g=diagonalOneParameter v hv 1 * (completeRootChain n).word u := by
  let v : Fin n → ℝ := fun i => Real.log (g.val i i)
  have hprod : ∏ i, g.val i i=1 := (Matrix.det_of_isUpperTriangular htri).symm.trans g.prop
  have hv : ∑ i, v i=0 := by
    dsimp [v]
    rw [←Real.log_prod (fun i _ => (hpos i).ne'),hprod,Real.log_one]
  let a := diagonalOneParameter v hv 1
  let u : G n := a⁻¹*g
  have hu : PositiveRootPattern (allPositiveRoots n) u := by
    intro i j hij
    have hij' : ¬ i < j := by simpa [allPositiveRoots] using hij
    have he : u.val i j=Real.exp (-v i)*g.val i j := by
      change ((diagonalOneParameter v hv 1)⁻¹*g).val i j = _
      rw [←diagonalOneParameter_neg]
      change (Matrix.diagonal (fun i => Real.exp (v i*(-1))) * g.val) i j = _
      rw [Matrix.diagonal_mul]
      congr 2
      ring
    rw [he]
    by_cases heq : i=j
    · subst j
      rw [Matrix.one_apply_eq]
      dsimp [v]
      rw [Real.exp_neg,Real.exp_log (hpos i),inv_mul_cancel₀ (hpos i).ne']
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij') (Ne.symm heq)
      rw [htri hji,Matrix.one_apply_ne heq,mul_zero]
  have hum : u ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootPattern_mem_generated (allPositiveRoots n)
      (fun p hp => (Finset.mem_filter.mp hp).2) (allPositiveRoots_closed n) hu
  obtain ⟨t,ht⟩ := upperRootWord_surjective n ⟨u,hum⟩
  refine ⟨v,hv,t,?_⟩
  rw [ht]
  change g=a*(a⁻¹*g)
  group

/-- A sufficiently small future lift has a neutral diagonal part. Its
remaining part belongs to the genuine strong stable unipotent group. -/
theorem small_weak_stable_factorization {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (hord : StrictMono ell) (g : G n) (hg : g ∈ matrixBall n 1)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0) :
    ∃ (v : Fin n → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime n),
      g=diagonalOneParameter v hv 1 * (completeRootChain n).word u ∧
      ∀ t : ℝ, Commute (diagonalOneParameter v hv 1) (diagonalOneParameter ell hell t) := by
  have htri : g.val.IsUpperTriangular := fun i j hji => hzero i j (hord hji)
  have hpos (i : Fin n) : 0 < g.val i i := by
    have hh := hg i i
    rw [Matrix.one_apply_eq] at hh
    have hh' := (abs_lt.mp hh).1
    linarith
  obtain ⟨v,hv,u,hu⟩ := upper_triangular_positive_diagonal_factorization g htri hpos
  refine ⟨v,hv,u,hu,?_⟩
  intro t
  apply commute_diagonalOneParameter_of_weight_support ell hell
  intro i j hij
  have hne : i ≠ j := by intro he; exact hij (congrArg ell he)
  change (Matrix.diagonal (fun i => Real.exp (v i*1))) i j=0
  exact Matrix.diagonal_apply_ne _ hne

end DukePrimeDegree

end

end OAI
