import OAI.NumberTheory.DukePrimeDegree.Geometry.TransverseRootFibers
import OAI.NumberTheory.DukePrimeDegree.Geometry.WeakStableFactorization

namespace OAI

/-! # Fine transverse returns remove the weak stable diagonal -/

noncomputable section
open Matrix Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem upperRootWord_of_fine_transverse_returns {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (g : G n) (hg : g ∈ matrixBall n 1)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0)
    (hfine : ∀ ε : ℝ, 0 < ε → ∃ (k : ℕ)
      (s r : UpperRootTransverse n) (u w : UpperRootTime n),
      upperRootParam n (s,u)*(diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ)))=upperRootParam n (r,w) ∧
      ∀ i, |transverseLogDiagonal r i-transverseLogDiagonal s i| < ε) :
    ∃ v : UpperRootTime n, (completeRootChain n).word v=g := by
  obtain ⟨v,hv,t,hg',hcomm⟩ := small_weak_stable_factorization ell hell hord g hg hzero
  have hfactor (k : ℕ) :
      diagonalOneParameter ell hell (k:ℝ)*g*diagonalOneParameter ell hell (-(k:ℝ)) =
        diagonalOneParameter v hv 1 *
          (completeRootChain n).word ((completeRootChain n).rootDilation ell (k:ℝ) t) := by
    rw [hg',(completeRootChain n).word_rootDilation ell hell (k:ℝ)]
    calc
      _ = (diagonalOneParameter ell hell (k:ℝ)*diagonalOneParameter v hv 1)*
          ((completeRootChain n).word t*diagonalOneParameter ell hell (-(k:ℝ))) := by group
      _ = (diagonalOneParameter v hv 1*diagonalOneParameter ell hell (k:ℝ))*
          ((completeRootChain n).word t*diagonalOneParameter ell hell (-(k:ℝ))) := by
            rw [(hcomm (k:ℝ)).eq]
      _ = _ := by group
  have hlog (k : ℕ) (s r : UpperRootTransverse n) (u w : UpperRootTime n)
      (hk : upperRootParam n (s,u)*(diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ)))=upperRootParam n (r,w)) :
      transverseLogDiagonal r=fun i => transverseLogDiagonal s i+v i := by
    rw [hfactor k] at hk
    simpa only [mul_one] using transverseLogDiagonal_right_diagonal_upperRoot
      s r u w v hv 1
      ⟨_,upperRootWord_mem n _⟩ hk
  have hvzero : v=0 := by
    funext i
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    by_contra hn
    obtain ⟨k,s,r,u,w,he,hk⟩ := hfine |v i| (lt_of_not_ge hn)
    have hi := hk i
    rw [hlog k s r u w he] at hi
    simp only [add_sub_cancel_left,lt_self_iff_false] at hi
  have ha : diagonalOneParameter v hv 1=1 := by
    apply Subtype.ext
    ext i j
    simp [diagonalOneParameter,hvzero,Matrix.one_apply]
  exact ⟨t,by simpa only [ha,one_mul] using hg'.symm⟩

theorem upperRootWord_of_fine_transverse_conjugates {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (g : G n) (hg : g ∈ matrixBall n 1)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0)
    (s r : ℕ → UpperRootTransverse n) (u w : ℕ → UpperRootTime n)
    (he : ∀ k : ℕ, upperRootParam n (s k,u k)*
      (diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ)))=upperRootParam n (r k,w k))
    (hfine : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ i,
      |transverseLogDiagonal (r k) i-transverseLogDiagonal (s k) i| < ε) :
    ∃ v : UpperRootTime n, (completeRootChain n).word v=g := by
  apply upperRootWord_of_fine_transverse_returns ell hell hord g hg hzero
  intro ε hε
  obtain ⟨k,hk⟩ := hfine ε hε
  exact ⟨k,s k,r k,u k,w k,he k,hk⟩

end DukePrimeDegree

end

end OAI
