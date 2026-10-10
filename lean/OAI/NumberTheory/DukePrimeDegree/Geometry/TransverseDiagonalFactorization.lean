import OAI.NumberTheory.DukePrimeDegree.Geometry.TransverseDiagonalData

namespace OAI

/-! # Exact neutral fibers of the transverse coordinate map

On the positive-diagonal chart, equality of column ratios means that two
transverse points differ by an actual positive diagonal matrix. This
identifies the neutral coordinates without an abstract quotient factor.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootTransverse_diagonal_prod {n : ℕ} (s : UpperRootTransverse n) :
    ∏ i, s.val.val i i=1 :=
  (Matrix.det_of_isLowerTriangular s.val.val (upperRootTransverse_lowerTriangular s)).symm.trans
    s.val.prop

lemma transverse_positive_same_ratios_iff {n : ℕ} (s r : UpperRootTransverse n)
    (hs : ∀ i, 0 < s.val.val i i) (hr : ∀ i, 0 < r.val.val i i) :
    transverseColumnRatios s=transverseColumnRatios r ↔
      ∃ (v : Fin n → ℝ) (hv : ∑ i, v i=0),
        r=upperRootTransverseDiagonal v hv 1 s := by
  constructor
  · intro hrat
    let v : Fin n → ℝ := fun i => Real.log (r.val.val i i/s.val.val i i)
    have hv : ∑ i, v i=0 := by
      dsimp [v]
      rw [←Real.log_prod (fun i _ => (div_pos (hr i) (hs i)).ne'),
        Finset.prod_div_distrib,upperRootTransverse_diagonal_prod r,
        upperRootTransverse_diagonal_prod s,div_self one_ne_zero,Real.log_one]
    refine ⟨v,hv,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    change r.val.val i j=(s.val*diagonalOneParameter v hv 1).val i j
    rw [mul_diagonalOneParameter_entry]
    have he : Real.exp (v j*1)=r.val.val j j/s.val.val j j := by
      dsimp [v]
      rw [mul_one,Real.exp_log (div_pos (hr j) (hs j))]
    rw [he,←mul_div_assoc]
    apply (eq_div_iff (hs j).ne').mpr
    have h := congrFun (congrFun hrat i) j
    change s.val.val i j/s.val.val j j=r.val.val i j/r.val.val j j at h
    exact ((div_eq_div_iff (hs j).ne' (hr j).ne').mp h).symm
  · rintro ⟨v,hv,rfl⟩
    exact (transverseColumnRatios_diagonal v hv 1 s).symm

lemma transverse_positive_same_ratios_neutral {n : ℕ} (s r : UpperRootTransverse n)
    (hs : ∀ i, 0 < s.val.val i i) (hr : ∀ i, 0 < r.val.val i i)
    (h : transverseColumnRatios s=transverseColumnRatios r)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) :
    ∃ a : G n, r.val=s.val*a ∧
      ∀ t : ℝ, Commute a (diagonalOneParameter ell hell t) := by
  obtain ⟨v,hv,he⟩ := (transverse_positive_same_ratios_iff s r hs hr).mp h
  refine ⟨diagonalOneParameter v hv 1,congrArg Subtype.val he,?_⟩
  intro t
  change diagonalOneParameter v hv 1 * diagonalOneParameter ell hell t =
    diagonalOneParameter ell hell t * diagonalOneParameter v hv 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (Matrix.diagonal (fun k => Real.exp (v k*1)) *
      Matrix.diagonal (fun k => Real.exp (ell k*t))) i j =
    (Matrix.diagonal (fun k => Real.exp (ell k*t)) *
      Matrix.diagonal (fun k => Real.exp (v k*1))) i j
  rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  simp only [mul_comm]

end DukePrimeDegree

end

end OAI
