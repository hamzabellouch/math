import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarLocalization
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellBottom

namespace OAI

/-! The published negative-ground-energy gap consequence used conditionally.

Gerald Teschl, *Mathematical Methods in Quantum Mechanics*, second edition,
AMS Graduate Studies in Mathematics 157 (2014), Theorems 10.2, 10.13 and
4.12 (including its quadratic-form-domain version).
Author's text: https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe2.pdf

For a bounded compactly supported real potential in dimension two, Theorem
10.2 gives the self-adjoint Schrödinger operator, its smooth compact core and
essential spectrum `[0,∞)`. Theorem 10.13 makes an attained ground energy
simple. At a negative ground energy the next max-min value is strictly larger;
Theorem 4.12 states the corresponding inequality on the form domain. Below
we assume only that useful form consequence, then apply it to the actual
manufactured well and its attained bottom. The spectral consequence is
a premise of this conditional interface. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instSpectralInputMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instSpectralInputBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instSpectralInputMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

def compactPotentialForm (W : Test) (u : Sobolev) : ℝ :=
  (1 / 2 : ℝ) * ‖u.val.2‖ ^ 2 +
    inner ℝ u.val.1 ((testScalarField W ℝ).operator u.val.1)

/-- The negative-ground-energy specialization of Teschl's Theorems 10.2,
10.13 and 4.12. Its premises and conclusion concern the actual closed H¹
graph and the actual multiplication operator for a compact C¹ potential. -/
def PublishedNegativePlanarGroundGap : Prop :=
  ∀ (W : Test) (E : ℝ) (g : Sobolev), E < 0 → ‖g.val.1‖ ^ 2 = 1 →
    (∀ u : Sobolev, E * ‖u.val.1‖ ^ 2 ≤ compactPotentialForm W u) →
    compactPotentialForm W g = E →
    ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev,
      inner ℝ u.val.1 g.val.1 = 0 →
      (E + γ) * ‖u.val.1‖ ^ 2 ≤ compactPotentialForm W u

theorem compactPotentialForm_well (u : Sobolev) :
    compactPotentialForm wellTest u = form u.val := by
  simp only [compactPotentialForm, form, wellTest_operator]

/-- The single well-specific consequence actually used by the construction. -/
def ManufacturedPlanarGroundGap : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev,
    inner ℝ u.val.1 normalizedMode.val.1 = 0 →
    ((-1/2:ℝ)+γ)*‖u.val.1‖^2 ≤ form u.val

/-- Conditional gap for the actual resolvent-generated well, using only the
published spectral consequence above. Membership, normalization and energy
of this specific mode and the all-domain lower bound are proved separately. -/
theorem manufacturedPlanarWell_gap (hpublished : PublishedNegativePlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev,
      inner ℝ u.val.1 normalizedMode.val.1 = 0 →
      ((-1 / 2 : ℝ) + γ) * ‖u.val.1‖ ^ 2 ≤ form u.val := by
  obtain ⟨γ, hγ, hbound⟩ := hpublished wellTest (-1 / 2) normalizedMode (by norm_num)
    normalizedMode_mass
    (fun u => by simpa only [compactPotentialForm_well, neg_div] using form_lower u)
    (by simpa only [compactPotentialForm_well, neg_div] using normalizedMode_energy)
  exact ⟨γ, hγ, fun u hu => (hbound u hu).trans_eq (compactPotentialForm_well u)⟩

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
