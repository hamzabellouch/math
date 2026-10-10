import OAI.Geometry.IsometricImmersion.Taylor.TaylorCauchyData
import OAI.Geometry.IsometricImmersion.Darboux.QSameStripMargins
import OAI.Geometry.IsometricImmersion.Calculus.ShearHeightJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Pulse SmoothLocal.Flow

def initialShearedStateBudget (Z q0 : ℝ) : ℝ :=
  max 1 ((2*(1+|q0|))^2*Z)

theorem initialShearedStateBudget_nonneg (Z q0 : ℝ) : 0 ≤ initialShearedStateBudget Z q0 :=
  zero_le_one.trans (le_max_left _ _)

theorem actual_initial_sheared_state_bound
    {z : Coord → ℝ} {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : modelSquare ⊆ U) {Z : ℝ} (hZ : 0 ≤ Z)
    (hjet : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (q0 left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, inverseShearCoordinates q0 ![x,a] ∈ modelSquare)
    {x : ℝ} (hx : x ∈ Ioo left right) (hpB : ‖(![x,a] : Coord)‖ ≤ 1) :
    ‖qSolutionJet (linearCauchy a (heightCauchyValue (heightInShearCoordinates z q0) a)
      (heightCauchyVelocity (heightInShearCoordinates z q0) a)) ![x,a]‖ ≤
        initialShearedStateBudget Z q0 := by
  have hz2 : CoordinateBound z modelSquare 2 Z := by
    apply coordinateBound_of_frechet_bounds hz hU hSU
    intro k hk p hp
    exact hjet k (by omega) p hp
  have hzs := heightInShearCoordinates_contDiffOn hz q0
  have hV := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  rw [linearCauchy_height_initial_state hzs hV left right a
    (fun x hx => hSU (hcut x hx)) hx]
  have hb := SmoothLocal.Pulse.CoordinateBound.inverse_shear hz2 hz hU hSU hZ q0
  apply qSolutionJet_norm_bound_of_words (by norm_num) hpB
  intro ds hds
  exact hb ds hds _ (hcut x hx)

end SmoothLocal.Taylor

end

end OAI
