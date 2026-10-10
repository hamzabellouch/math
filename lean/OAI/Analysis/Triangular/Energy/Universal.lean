import OAI.Analysis.Triangular.Energy.Gaussian
import OAI.Analysis.Triangular.Energy.Potentials

namespace OAI

noncomputable section
namespace AtomicTriangular
/-- The triangular lattice minimizes every nonnegative completely monotone energy. -/
theorem universal_energy_minimum (g : ℝ → ℝ) (C : Set Plane)
    (hg : AdmissiblePotential g) (_hC : LocallyFinite C) (hd : DensityOne C) :
    latticeEnergy g ≤ energy g C ∧ latticeEnergy g = energy g A := by
  have hb (α : ℝ) (hα : 0<α) :
      TriangularUniversal.latticeEnergy (TriangularUniversal.gaussPot α)≤
        TriangularUniversal.energy (TriangularUniversal.gaussPot α) C := by
    rw [←latticeEnergy_eq_support]
    exact gaussian_energy_bound hd α hα
  have hu := TriangularUniversal.universal_from_gaussian_bounds hd hb hg
  constructor
  · rw [latticeEnergy_eq_support]
    exact hu.1
  · rw [latticeEnergy_eq_support,A_eq_support]
    exact hu.2
end AtomicTriangular
end

end OAI
