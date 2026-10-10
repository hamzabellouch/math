import OAI.Geometry.NodalSets.Elliptic.RealWeakConvolution
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetPairings

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff Convolution
noncomputable section

theorem real_weak_jet_convolution {n : ℕ}
    (U : List (Fin n) → Coord n → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N → LocallyIntegrable (U es) volume)
    (hw : ∀ es, es.length < N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, U es x*coordPartial psi x i)=-(∫ x, U (i::es) x*psi x))
    (k : Coord n → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (ds : List (Fin n)) (hd : ds.length ≤ N) :
    partialJet (U [] ⋆ k) ds=U ds ⋆ k := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    have hlt : ds.length < N := by simp only [List.length_cons] at hd; omega
    change (fun x ↦ coordPartial (partialJet (U [] ⋆ k) ds) x i)=_
    rw [ih (by omega)]
    exact real_weak_convolution_derivative (U ds) (U (i::ds)) k (hU ds (by omega)) hk hc i (hw ds hlt i)

end
end Yau

end OAI
