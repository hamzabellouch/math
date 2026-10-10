import OAI.MeasureTheory.Falconer.Radial.RadialSphereLaw

namespace OAI

/-! # Deleting original pairs whose witness direction is exceptional -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialBadWitness (w₀ : Sphere d) (G : Set (Space d × Space d))
    (B : Set (Sphere d)) : Set (Space d × Space d) :=
  G ∩ {p | normalizeToSphere w₀ (p.2-p.1) ∈ B}

theorem radialBadWitness_measurable (w₀ : Sphere d) {G : Set (Space d × Space d)}
    (hG : MeasurableSet G) {B : Set (Sphere d)} (hB : MeasurableSet B) :
    MeasurableSet (radialBadWitness w₀ G B) :=
  hG.inter (hB.preimage ((normalizeToSphere_measurable w₀).comp
    (measurable_snd.sub measurable_fst)))

theorem radial_bad_witness_mass (w₀ : Sphere d) (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (B : Set (Sphere d)) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤ c) :
    (μ.prod ν) (radialBadWitness w₀ G B) ≤ c*μ univ := by
  rw [Measure.prod_apply (radialBadWitness_measurable w₀ hG hB)]
  have he (z : Space d) : ν {x | (z,x) ∈ radialBadWitness w₀ G B} =
      originalRadialSphereLaw w₀ ν G z B := by
    rw [originalRadialSphereLaw_apply w₀ ν G z B hB]
    rfl
  change (∫⁻ z, ν {x | (z,x) ∈ radialBadWitness w₀ G B} ∂μ) ≤ c*μ univ
  simp_rw [he]
  exact (lintegral_mono_ae hsmall).trans_eq (lintegral_const c)

theorem direction_good_of_not_radialBadWitness (w₀ : Sphere d)
    (G : Set (Space d × Space d)) (B : Set (Sphere d)) {z x : Space d}
    (hgood : (z,x) ∈ G \ radialBadWitness w₀ G B) :
    normalizeToSphere w₀ (x-z) ∉ B := by
  intro hb
  exact hgood.2 ⟨hgood.1,hb⟩

end Falconer

end OAI
