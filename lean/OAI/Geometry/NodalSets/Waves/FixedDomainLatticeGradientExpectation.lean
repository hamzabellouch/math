import OAI.Geometry.NodalSets.Elliptic.RescaledGradientExpectation
import OAI.Geometry.NodalSets.Waves.FixedDomainLatticeDerivativeMoments
import OAI.Geometry.NodalSets.Waves.LatticeGradientExpectation

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_gradient_expectation_fixed_domain
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ C > 0, ∀ (w S S0 T0 : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0), IsCompact D → D ⊆ H → ∀ (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → 5 ≤ k0 →
      ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∃ G : ((SourceGrid U n × Fin 3) × Fin 2 → ℝ) → ℝ,
          Continuous G ∧ Integrable G gaussianPairs ∧ (∀ coeff, 0 ≤ G coeff) ∧
          (∫ coeff, G coeff ∂gaussianPairs) ≤ C ∧
          ∀ coeff L, 0 ≤ L →
            (G coeff ≤ L ↔ ∀ v : Coord, sourceEuclideanNorm v ≤ 1 →
              sourceEuclideanNorm (fun j ↦ fderiv ℝ (rescaledGaussianField
                (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
                S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x coeff)
                  v (Pi.single j 1)) ≤ L) := by
  obtain ⟨B,hB,hmom⟩ := lattice_derivative_second_moments_fixed_domain g hH hg hp 5
  refine ⟨648*(B+1),by positivity,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 hd gamma hgamma hgap
  filter_upwards [hmom w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hd gamma hgamma hgap,a.estimates] with n hn hest
  obtain ⟨hfin,hn⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
  exact rescaled_gradient_supremum_expectation V hV S0 T0 S hS0 hT0
    n (sourceSignScale g S x) (a.latticeSigma hUD n x) x hB.le
    (fun v hv k hk dirs hd ↦ (hn x hx v hv k hk dirs hd).2)

end
end Yau.Geometry

end OAI
