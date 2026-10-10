import OAI.Geometry.RCD.Sobolev.CompactEnergyDensity
import OAI.Geometry.RCD.Sobolev.FiniteEnergyRepresentatives
import OAI.Geometry.RCD.Sobolev.WeakLaplacianDomain

namespace OAI

/-! # Sobolev representatives of mixed gradients of regular compact functions -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_mixed_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)
    (f g : SobolevSpace (hausdorff n X) hX.quadratic)
    {φ ψ : X → ℝ} {L M : ℝ≥0}
    (hφ : LipschitzWith L φ) (hcφ : HasCompactSupport φ)
    (hf : SobolevSpace.toLp (hausdorff n X) hX.quadratic f =ᵐ[hausdorff n X] φ)
    (hψ : LipschitzWith M ψ) (hcψ : HasCompactSupport ψ)
    (hg : SobolevSpace.toLp (hausdorff n X) hX.quadratic g =ᵐ[hausdorff n X] ψ)
    (df dg : Lp ℝ 2 (hausdorff n X))
    (hdf : IsWeakLaplacian (hausdorff n X) hX.quadratic f df)
    (hdg : IsWeakLaplacian (hausdorff n X) hX.quadratic g dg) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic f g := by
  let μ := hausdorff n X
  obtain ⟨A,hA,-,-⟩ := hX.compact_energy_density hn hφ hcφ p f hf df hdf
  obtain ⟨B,hB,-,-⟩ := hX.compact_energy_density hn hψ hcψ p g hg dg hdg
  have hab : SobolevSpace.toLp μ hX.quadratic (f+g) =ᵐ[μ] φ+ψ := by
    simpa only [map_add] using (Lp.coeFn_add (SobolevSpace.toLp μ hX.quadratic f)
      (SobolevSpace.toLp μ hX.quadratic g)).trans (hf.add hg)
  obtain ⟨C,hC,-,-⟩ := hX.compact_energy_density hn (hφ.add hψ) (hcφ.add hcψ)
    p (f+g) hab (df+dg) (hdf.add μ hX.quadratic hdg)
  refine ⟨(1/2 : ℝ) • (C-A-B),?_⟩
  have h := polarized_energy_representative μ hX.quadratic (Ω := univ) f g A B C
    (by simpa only [Measure.restrict_univ] using hA)
    (by simpa only [Measure.restrict_univ] using hB)
    (by simpa only [Measure.restrict_univ] using hC)
  simpa only [Measure.restrict_univ] using h

end RegularPointCoordinates

end

end OAI
