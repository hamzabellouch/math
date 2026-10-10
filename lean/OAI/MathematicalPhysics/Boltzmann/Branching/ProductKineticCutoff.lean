import OAI.MathematicalPhysics.Boltzmann.Branching.InteriorCell
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocitySmoothingError
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapPairMoments

namespace OAI

/-! # Kinetic cutoffs preserving velocity tests on a spacetime patch -/

noncomputable section

open Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.Compactness

def productCutoff (χ : Published.SpaceTime → ℝ) (β : Velocity → ℝ)
    (z : Published.KineticPhase) : ℝ := χ z.1*β z.2

theorem productCutoff_tsupport (χ : Published.SpaceTime → ℝ) (β : Velocity → ℝ) :
    tsupport (productCutoff χ β) ⊆ tsupport χ ×ˢ tsupport β := by
  apply closure_minimal ?_ ((isClosed_tsupport χ).prod (isClosed_tsupport β))
  intro z hz
  have hne := mul_ne_zero_iff.mp hz
  exact ⟨subset_tsupport χ hne.1,subset_tsupport β hne.2⟩

theorem productCutoff_compact {χ : Published.SpaceTime → ℝ} {β : Velocity → ℝ}
    (hχ : HasCompactSupport χ) (hβ : HasCompactSupport β) :
    HasCompactSupport (productCutoff χ β) :=
  (hχ.prod hβ).of_isClosed_subset (isClosed_tsupport _) (productCutoff_tsupport χ β)

theorem productCutoff_smooth {χ : Published.SpaceTime → ℝ} {β : Velocity → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) :
    ContDiff ℝ (⊤ : ℕ∞) (productCutoff χ β) :=
  (hχ.comp contDiff_fst).mul (hβ.comp contDiff_snd)

theorem productCutoff_in_cell {χ : Published.SpaceTime → ℝ} (β : Velocity → ℝ)
    (hs : tsupport χ ⊆ TorusKineticChart.interiorRegion) :
    tsupport (productCutoff χ β) ⊆ {z | z.1.2 ∈ TorusChart.cube} := by
  intro z hz
  change z.1.2 ∈ TorusChart.cube
  exact interior_subset (hs ((productCutoff_tsupport χ β hz).1)).2

theorem productCutoff_initial_zero {χ : Published.SpaceTime → ℝ} (β : Velocity → ℝ)
    (hs : tsupport χ ⊆ TorusKineticChart.interiorRegion) (p : Velocity × Velocity) :
    productCutoff χ β (characteristic p 0) = 0 := by
  have hn : (0,p.1) ∉ tsupport χ := fun h => lt_irrefl (0 : ℝ) (hs h).1
  have hz := image_eq_zero_of_notMem_tsupport hn
  simp only [productCutoff,characteristic,zero_smul,add_zero,hz,zero_mul]

theorem productCutoff_preserves_test (χ : Published.SpaceTime → ℝ)
    {β ψ : Velocity → ℝ} (hβ : ∀ v, ψ v*β v = ψ v) :
    JetCopyDatum.averageWeight (productCutoff χ β) ψ = fun z => χ z.1*ψ z.2 := by
  funext z
  change ψ z.2*(χ z.1*β z.2) = χ z.1*ψ z.2
  calc
    _ = χ z.1*(ψ z.2*β z.2) := by ring
    _ = _ := by rw [hβ]

end BoltzmannNonuniqueness.Compactness

end

end OAI
