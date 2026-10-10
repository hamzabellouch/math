import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootGlobalCoordinates

namespace OAI

/-!
# Diagonal dynamics in ordered upper-root coordinates

Conjugation by a diagonal element is exactly the product of the root
coordinate dilations, with each factor carrying its own root weight.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def rootDilation : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → (Fin n → ℝ) → ℝ → c.Time ≃ₜ c.Time
  | _, _, .done, _, _ => Homeomorph.refl _
  | _, _, .step a b _ _ _ tail, ell, r =>
      (tail.rootDilation ell r).prodCongr
        (Homeomorph.mulLeft₀ (Real.exp ((ell a - ell b) * r)) (Real.exp_ne_zero _))

theorem word_rootDilation (c : EliminationChain P D) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (r : ℝ) (t : c.Time) :
    c.word (c.rootDilation ell r t) =
      diagonalOneParameter ell hell r * c.word t * diagonalOneParameter ell hell (-r) := by
  induction c with
  | done =>
      change 1 = diagonalOneParameter ell hell r * 1 * diagonalOneParameter ell hell (-r)
      rw [mul_one, diagonalOneParameter_neg, mul_inv_cancel]
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change tail.word (tail.rootDilation ell r t.1) *
        Matrix.SpecialLinearGroup.transvection hab (Real.exp ((ell a - ell b) * r) * t.2) =
          diagonalOneParameter ell hell r *
            (tail.word t.1 * Matrix.SpecialLinearGroup.transvection hab t.2) *
              diagonalOneParameter ell hell (-r)
      rw [ih, ←diagonal_conjugation_transvection ell hell hab t.2 r,
        diagonalOneParameter_neg]
      group

end EliminationChain

theorem upperRootWord_diagonal (n : ℕ) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (r : ℝ) (t : UpperRootTime n) :
    (upperRootWordHomeomorph n ((completeRootChain n).rootDilation ell r t)).val =
      diagonalOneParameter ell hell r * (upperRootWordHomeomorph n t).val *
        diagonalOneParameter ell hell (-r) :=
  (completeRootChain n).word_rootDilation ell hell r t

theorem upperRoot_orbit_diagonal (n : ℕ) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (r : ℝ) (x : X n) (t : UpperRootTime n) :
    rightAction (rightAction x (upperRootWordHomeomorph n t).val)
        (diagonalOneParameter ell hell r) =
      rightAction (rightAction x (diagonalOneParameter ell hell r))
        (upperRootWordHomeomorph n ((completeRootChain n).rootDilation ell (-r) t)).val := by
  rw [rightAction_mul, rightAction_mul, upperRootWord_diagonal n ell hell (-r) t, neg_neg,
    diagonalOneParameter_neg]
  congr 1
  group

end DukePrimeDegree

end

end OAI
