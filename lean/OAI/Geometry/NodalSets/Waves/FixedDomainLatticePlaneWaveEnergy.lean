import OAI.Geometry.NodalSets.Elliptic.FrequencyDerivativeEnergy
import OAI.Geometry.NodalSets.Waves.FixedDomainLatticeFrequencyAnnulus
import OAI.Geometry.NodalSets.Waves.LatticeFullPlaneWaveApprox
import OAI.Geometry.NodalSets.Waves.LatticeNormalizedWeights
import OAI.Geometry.NodalSets.Waves.LatticePlaneWaveEnergy

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_planeWave_derivative_energy_fixed_domain
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) (d : ℕ) :
    ∃ C > 0, ∀ (w S : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0), IsCompact D → D ⊆ H → ∀ (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∀ v : Coord, ∀ k : ℕ, k ≤ d →
        ∑ i : SourceGrid U n × Fin 3,
          ‖iteratedFDeriv ℝ k
            (a.latticePlaneWaveCoefficient hUD n x (sourceSignScale g S x) i) v‖^2 ≤ C := by
  obtain ⟨κ,hκ,B,hB,hann⟩ := lattice_main_frequency_annulus_fixed_domain g hH hg hp
  let B' := max 1 B
  let C := ((d.factorial:ℝ)*(4*B')^d)^2
  have hB' : 1 ≤ B' := le_max_left _ _
  have h4 : 1 ≤ 4*B' := by linarith
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
  filter_upwards [hann w S D U m J K k0 a hD hDH hUD hUH,
    a.latticeAlpha_main_mass hUD hU hUb hQ hQU (1/2) (by norm_num)] with n hn hm
  obtain ⟨hfin,hm⟩ := hm
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v k hk
  apply (a.latticePlaneWaveCoefficient_energy hUD n x _ hB' (by rw [(hm x hx).1])
    (fun i hi ↦ ((hn x (hUD (hQU hx)) i hi).2).trans (le_max_right _ _)) k v).trans
  have hf : (k.factorial:ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hk
  have hpow := pow_le_pow_right₀ h4 hk
  dsimp [C]
  gcongr

end
end Yau.Geometry

end OAI
