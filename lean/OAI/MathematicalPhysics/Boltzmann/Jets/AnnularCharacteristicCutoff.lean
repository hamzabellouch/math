import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricAnnularFrequency
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularTightness

namespace OAI

/-! # One smooth cutoff and one physical clock for a whole short annular window -/

noncomputable section
open Set MeasureTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem exists_annular_characteristic_cutoff {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ ≤ 1) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η α γ K b W : ℝ},
      (hθ : 0 < θ) → 0 < η → η ≤ Real.log (1+(1/4:ℝ)/20) →
      (hα : 0 ≤ α) → α ≤ 1/4 → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 ≤ K → 0 < b → W ≤ κ*b/200 → ∀ l : ℝ,
      ∃ β : (Velocity × Velocity) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
        (∀ p, 0 ≤ β p) ∧ (∀ p, β p ≤ 1) ∧
        (∀ p, ‖p.1+b • p.2-(κ*b) • firstAxis‖ ≤ κ*b/4 → ‖p.2‖ ≤ 6 → β p = 1) ∧
        (∀ u : CharacteristicPhase, u.1 ∈ Icc b (b+W) → u.2 ∈ tsupport β →
          frequency θ η l K α γ u.1
            (transverse (u.2.1+u.1 • u.2.2),axial (u.2.1+u.1 • u.2.2)) u.2.2 ≤
              48*Real.pi*K/(κ*b)) := by
  have hM : 1 ≤ 16/κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨γ₀,hγ₀,hbound⟩ := annular_frequency_bound hM
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η α γ K b W hθ hη hηsmall hα hαsmall hγ hγsmall hK hb hW l
  obtain ⟨β,hβ,hβc,hβn,hβ₁,hcore,hsupp⟩ :=
    exists_characteristic_phase_cutoff b ((κ*b) • firstAxis) (show 0 < κ*b/4 by positivity)
  refine ⟨β,hβ,hβc,hβn,hβ₁,hcore,?_⟩
  intro u hu hus
  have hp := hsupp u.2 hus
  have hd := phase_displacement_bound hu hp.1 hp.2
  have hx : ‖u.2.1+u.1 • u.2.2-(κ*b) • firstAxis‖ ≤ κ*b/2+7*W := by
    convert hd using 1; ring
  have hgeo := annular_window_bounds hκ hκsmall hb hW hu hx
  have hh := hbound hθ hη hηsmall hα hαsmall hγ hγsmall hK
    (hb.le.trans hu.1) (show 0 < κ*b/4 by positivity) l (u.2.1+u.1 • u.2.2) u.2.2
    hgeo.1 hgeo.2.1 hgeo.2.2 hp.2
  convert hh using 1; field_simp

end BoltzmannNonuniqueness.GeometricBackground

end

end OAI
