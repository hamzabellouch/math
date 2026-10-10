import Mathlib
import OAI.Probability.Ballisticity.Estimates.CountableProdBind

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma rawPair_gap_mass_composition {d : ℕ} (e f : Direction d) (k m : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) (π : Measure (Lattice d × Lattice d))
    (c b : ℝ≥0∞) (z : ℝ) (hπ : c • π ≤ rawPairEndpointLaw (realPosition (step e)) k ω x)
    (hm : b ≤ pairKernelMass (realPosition (step e)) f m z π ω) :
    c*b ≤ rawPairEndpointLaw (realPosition (step e)) (k+m) ω x {y | z ≤ signedCoordinate f (y.2-y.1)} := by
  have hbound := (rawPairMixture_mono (realPosition (step e)) m ω hπ).trans
    (rawPairEndpointLaw_comp_le e k m ω x)
  rw [rawPairMixture_smul] at hbound
  have hb := hbound {y | z ≤ signedCoordinate f (y.2-y.1)}
  simp only [Measure.smul_apply,smul_eq_mul,rawPairMixture_apply] at hb
  apply le_trans _ hb
  have hm' : b ≤ ∫⁻ y, rawPairEndpointLaw (realPosition (step e)) m ω y
      {z' | z ≤ signedCoordinate f (z'.2-z'.1)} ∂π := hm
  gcongr
end DirectionalTransience

end

end

end OAI
