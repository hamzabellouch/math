import OAI.Geometry.RCD.Harmonic.ProjectionRadialRows
import OAI.Geometry.RCD.Coordinates.RadialFitRestriction

namespace OAI

/-! # Restricting the actual radial rows to the centered projection coordinates -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
/-- Changing the representative of the local constant preserves the
restricted centered affine function. -/
theorem centered_affine_restrict_cutoff_eq {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (z a : Euclidean n)
    (s : Set X) (hs : μ s ≠ ∞) (eta chi : SobolevSpace μ hQ)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict s] fun _ => (1 : ℝ))
    (hchi : SobolevSpace.toLp μ hQ chi =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) :
    SobolevSpace.restrictLp μ hQ s (centeredAffineSobolev μ hQ u eta z a) =
      SobolevSpace.restrictLp μ hQ s (centeredAffineSobolev μ hQ u chi z a) := by
  rw [centeredAffineSobolev_restrict μ hQ u eta z a s hs
    (restrictLp_eq_one_of_representative μ hQ eta s hs heta),
    centeredAffineSobolev_restrict μ hQ u chi z a s hs
    (restrictLp_eq_one_of_representative μ hQ chi s hs hchi)]

omit [BorelSpace X] [ProperSpace X] in
/-- A row fit on the radial ball transfers to the smaller projection
ball and to the centered exact frame, with just the volume-ratio loss. -/
theorem normalized_centered_frame_fit {n : ℕ} {s t : Set X} (hts : t ⊆ s)
    (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) (hs0 : 0 < μ.real s) (ht0 : 0 < μ.real t)
    (u : Fin n → SobolevSpace μ hQ) (g eta chi : SobolevSpace μ hQ)
    (N : Euclidean n ≃L[ℝ] Euclidean n) (z a : Euclidean n)
    {C E : ℝ} (hE : 0 ≤ E) (hvol : μ.real s ≤ C * μ.real t)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict t] fun _ => (1 : ℝ))
    (hchi : SobolevSpace.toLp μ hQ chi =ᵐ[μ.restrict t] fun _ => (1 : ℝ))
    (hfit : ‖normalizeLocalL2 μ s hs (SobolevSpace.restrictLp μ hQ s
      (g - centeredAffineSobolev μ hQ u chi z a))‖ ^ 2 ≤ E) :
    let uc := centeredColumn μ hQ (transformedColumn μ hQ u N)
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) eta
    ‖normalizeLocalL2 μ t ht (SobolevSpace.restrictLp μ hQ t
      (g - sobolevColumnMap μ hQ uc (N.symm a)))‖ ^ 2 ≤ C * E := by
  dsimp only
  have hframe := centered_frame_covector_eq μ hQ u N eta z
    ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) a
    (by
      have hh := ContinuousLinearMap.adjoint_inner_left (N : Euclidean n →L[ℝ] Euclidean n)
        (N.symm a) z
      simpa only [ContinuousLinearEquiv.coe_coe, N.apply_symm_apply] using hh)
  rw [hframe, map_sub, centered_affine_restrict_cutoff_eq μ hQ u z a t ht eta chi heta hchi,
    ← map_sub]
  exact normalized_fit_restrict_sq μ hQ hts hs ht hs0 ht0 _ hE hvol hfit

/-- Centering a coordinate changes its local representative by a constant
and therefore preserves its pairing with the actual Poisson gradient. -/
theorem centered_radial_representative {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (f g eta : SobolevSpace μ hQ)
    (z : Euclidean n) (s : Set X) (j : Fin n)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict s] fun _ => (1 : ℝ))
    (hrep : SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict s]
      localGamma μ hQ f (u j)) :
    SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict s]
      localGamma μ hQ f (centeredColumn μ hQ u z eta j) := by
  have hd := localGamma_eq_of_constant_difference μ hQ s
    (centeredColumn μ hQ u z eta j) (u j) f (-z j)
    (centeredColumn_difference μ hQ u s z eta heta j)
  filter_upwards [hrep, hd, ae_restrict_of_ae (localGamma_comm μ hQ f (u j)),
    ae_restrict_of_ae (localGamma_comm μ hQ (centeredColumn μ hQ u z eta j) f)]
    with x hg hc hcomm hcomm'
  exact hg.trans (hcomm.trans (hc.symm.trans hcomm'))

end RegularPointCoordinates

end

end OAI
