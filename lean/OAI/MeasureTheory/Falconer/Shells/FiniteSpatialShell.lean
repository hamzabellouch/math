import OAI.MeasureTheory.Falconer.Shells.FiniteShellSum
import OAI.MeasureTheory.Falconer.Estimates.SpatialSharedRegularity

namespace OAI

/-! # Finite separated inverse terms in the independent angular shell

The spatial coefficient is the actual inverse-distance Fourier coefficient.
All radial and spatial integrability is derived from the bounded endpoint
families. The only energy hypotheses concern the two independent angles.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem finite_spatial_shell_sum_integrable {ι : Type*} (S : Finset ι)
    (_a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ι → ℕ)
    (U V : ι → Space d × (ℝ × Sphere d) → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (B C : ι → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ B i)
    (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ C i)
    (c : ι → ℝ → ℂ) (A : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ∀ i ∈ S, ‖c i r‖ ≤ A i) :
    Integrable (fun r => ‖∑ i ∈ S, c i r *
      spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i) r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  apply finite_shell_sum_sq_integrable (PlanarFalconer.sourceAngularShellMeasure v Ψ) S c
    (fun i => spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i)) A hc
  · intro i hi
    exact spatialSharedAmplitude_measurable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (U i) (V i) (hU i hi) (hV i hi)
  · intro i hi
    exact spatialSharedAmplitude_sq_integrable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (spatialFourierCoeff_integrable δ L hδ hL (j i))
      (U i) (V i) (hU i hi) (hV i hi) (hB i hi) (hC i hi)
      (hbU i hi) (hbV i hi) _
  · exact hA
  · exact hbound

theorem finite_spatial_shell_le {ι : Type*} (S : Finset ι)
    (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ι → ℕ)
    (U V : ι → Space d × (ℝ × Sphere d) → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (B C : ι → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ B i)
    (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ C i)
    (c : ι → ℝ → ℂ) (A H : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ∀ i ∈ S, ‖c i r‖ ≤ A i)
    (hH : ∀ i ∈ S, ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => U i (ξ,p)) (fun p => V i (ξ,p)) ≤ H i) :
    (2:ℝ)^((d:ℝ)*(v-a)) *
      (∫ r, ‖∑ i ∈ S, c i r *
        spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i) r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (S.card:ℝ)*∑ i ∈ S, (A i)^2*
        ((spatialFourierCost (d := d) δ L hδ hL (j i))^2*H i) := by
  apply finite_shell_sum_le S v Ψ c
    (fun i => spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i))
    A (fun i => (spatialFourierCost (d := d) δ L hδ hL (j i))^2*H i) hc
  · intro i hi
    exact spatialSharedAmplitude_measurable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (U i) (V i) (hU i hi) (hV i hi)
  · intro i hi
    exact spatialSharedAmplitude_sq_integrable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (spatialFourierCoeff_integrable δ L hδ hL (j i))
      (U i) (V i) (hU i hi) (hV i hi) (hB i hi) (hC i hi)
      (hbU i hi) (hbV i hi) _
  · exact hA
  · exact hbound
  · positivity
  · intro i hi
    exact spatial_fourier_shared_shell_le a v Ψ δ L hδ hL (j i)
      (U i) (V i) (hU i hi) (hV i hi) (hB i hi) (hC i hi)
      (hbU i hi) (hbV i hi) (H i) (hH i hi)

end Falconer

end OAI
