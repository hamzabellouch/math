import OAI.NumberTheory.DukePrimeDegree.Geometry.AtomicNeutralPatch
import OAI.NumberTheory.DukePrimeDegree.Geometry.TerminalNeutralPairs

namespace OAI

/-! # Whole-future pairs inside a graph patch differ by a neutral displacement -/

noncomputable section
open MeasureTheory Set Matrix
namespace DukePrimeDegree
open PrimeDegreePackets

theorem SmallNeutralPatch.graph_future_pair {n : ℕ} {ε : ℝ}
    (P : SmallNeutralPatch n ε)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (Q : X n → ℕ) (ρ : X n → ℝ)
    (hρ : ∀ x, ρ x ≤ 1) (hinj : ∀ x, LocalInjectivityAt (ρ x) x)
    (hlift : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g ∈ matrixBall n (ρ x), rightAction x g=y ∧
        ∀ i j, ell j < ell i → g.val i j=0)
    (F : Set (NeutralCoordinateBase n))
    (hF : ∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2)
    (x y : X n)
    (hx : x ∈ neutralQuotientParam n P.center ''
      ((P.base ×ˢ P.neutral) ∩ Prod.fst ⁻¹' F))
    (hy : y ∈ neutralQuotientParam n P.center ''
      ((P.base ×ˢ P.neutral) ∩ Prod.fst ⁻¹' F))
    (hε : ε ≤ ρ x)
    (hobs : fullFutureObservation
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
      fullFutureObservation
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y) :
    ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
      ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
  obtain ⟨z,⟨hz,hzF⟩,rfl⟩ := hx
  obtain ⟨w,⟨hw,hwF⟩,rfl⟩ := hy
  obtain ⟨g,hg,hgxy,hzero⟩ := hlift _ _ (fun k => by
    simpa only [fullFutureObservation,zero_add] using (congrFun hobs k).symm)
  have hchart := matrixBall_mono hε (P.small z hz w hw)
  obtain ⟨v,hv⟩ := neutral_graph_small_future_lift ell hord P.center F hF z w
    hzF hwF _ (hρ _) (hinj _) hchart g hg hzero hgxy
  refine ⟨g,matrixBall_mono (hρ _) hg,hgxy,?_⟩
  rw [hv]
  intro t
  apply commute_diagonalOneParameter_of_weight_support ell hell
  intro i j hij
  change (Matrix.diagonal (fun i => Real.exp (v.val i*1))) i j=0
  exact Matrix.diagonal_apply_ne _ (fun he => hij (congrArg ell he))

end DukePrimeDegree

end

end OAI
