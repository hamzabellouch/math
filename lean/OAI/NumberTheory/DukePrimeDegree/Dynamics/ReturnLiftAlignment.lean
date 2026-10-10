import OAI.NumberTheory.DukePrimeDegree.Dynamics.TransverseReturnCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.FineTransverseConjugates

namespace OAI

/-! # Aligning recurrent quotient lifts with transverse coordinates -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootBox_lift_alignment {n : ℕ} {a : G n} (B : UpperRootBox n a)
    (z w : B.domain) (ρ : ℝ)
    (hinj : Set.InjOn (fun g => rightAction (B.param z) g) (matrixBall n ρ))
    (hrel : (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈ matrixBall n ρ)
    (g : G n) (hg : g ∈ matrixBall n ρ)
    (hact : rightAction (B.param z) g=B.param w) :
    upperRootParam n z.val*g=upperRootParam n w.val := by
  have hc : rightAction (B.param z)
      ((upperRootParam n z.val)⁻¹*upperRootParam n w.val)=B.param w := by
    change Quotient.mk _ ((a*upperRootParam n z.val)*
      ((upperRootParam n z.val)⁻¹*upperRootParam n w.val)) =
        Quotient.mk _ (a*upperRootParam n w.val)
    congr 1
    group
  have he := hinj hg hrel (hact.trans hc.symm)
  rw [he]
  group

theorem upperRootWord_of_fine_recurrent_lifts {n : ℕ} {a : G n}
    (B : UpperRootBox n a)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (T : X n → X n) (S : Set (X n)) (hSB : S ⊆ B.range)
    (x y : X n) (g : G n) (hg : g ∈ matrixBall n 1)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0)
    (ρ : ℝ)
    (hinj : ∀ z : B.domain,
      Set.InjOn (fun h => rightAction (B.param z) h) (matrixBall n ρ))
    (hrel : ∀ z w : B.domain,
      (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈ matrixBall n ρ)
    (hsmall : ∀ k : ℕ, T^[k] x ∈ S →
      diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ)) ∈ matrixBall n ρ)
    (hlift : ∀ k : ℕ, rightAction (T^[k] x)
      (diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ)))=T^[k] y)
    (hfine : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, T^[k] x ∈ S ∧ T^[k] y ∈ S ∧
      ∀ z w : B.domain, B.param z=T^[k] x → B.param w=T^[k] y →
        ∀ i, |transverseLogDiagonal w.val.1 i-transverseLogDiagonal z.val.1 i| < ε) :
    ∃ v : UpperRootTime n, (completeRootChain n).word v=g := by
  apply upperRootWord_of_fine_transverse_returns ell hell hord g hg hzero
  intro ε hε
  obtain ⟨k,hkx,hky,hfine⟩ := hfine ε hε
  obtain ⟨z,hz⟩ := hSB hkx
  obtain ⟨w,hw⟩ := hSB hky
  refine ⟨k,z.val.1,w.val.1,z.val.2,w.val.2,?_,hfine z w hz hw⟩
  apply upperRootBox_lift_alignment B z w ρ (hinj z) (hrel z w)
    _ (hsmall k hkx)
  rw [hz,hw]
  exact hlift k

end DukePrimeDegree

end

end OAI
