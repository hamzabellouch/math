import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseCoupledPreparation

namespace OAI


                                      
section
namespace MetricKMedian.Preparation
open Finset
attribute [local instance] CoupledLaw.finite
variable {E T I : Type} [Fintype E] [DecidableEq E]
  [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I]

noncomputable def CoupledLaw.castWeights {D : E → Finset T} {a a' w w' : E → ℝ}
    {P : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw D a w P y p c g γ B Δ) (ha : a=a') (hw : w=w') :
    CoupledLaw D a' w' P y p c g γ B Δ where
  Ω := L.Ω
  ν := L.ν
  κ := L.κ
  O := L.O
  N := L.N
  R := L.R
  K := L.K
  C := L.C
  open_cap := by rw [← hw]; exact L.open_cap
  open_zero := by rw [← hw]; exact L.open_zero
  nominal_nonneg := L.nominal_nonneg
  nominal_cap := L.nominal_cap
  nominal_mean := by rw [← hw]; exact L.nominal_mean
  nominal_variance := by rw [← hw]; exact L.nominal_variance
  nominal_pair := by rw [← hw]; exact L.nominal_pair
  request_cap := L.request_cap
  request_target := L.request_target
  request_mean := by rw [← hw]; exact L.request_mean
  exact_total := L.exact_total
  half := L.half
  total_cap := L.total_cap
  total_deviation := L.total_deviation
  pieces := L.pieces
  piece_mean := L.piece_mean
  piece_pair := L.piece_pair
  piece_variance := L.piece_variance
  budget := by rw [← ha]; exact L.budget

end MetricKMedian.Preparation
end

end OAI
