import OAI.Probability.InvariantIsing.Spectral.SpectralTemperatureFunctional

namespace OAI

/-! The strict temperature tilt contradicts the energy order obtained from
contact tails. The energy sequence is the actual interaction observable
when this lemma is applied to contact minima. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma spectralContact_contradiction {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p q : OverlapPath) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (tk energy : ℕ → ℝ) (htk : Tendsto tk atTop (𝓝 t))
    (henergy : Tendsto energy atTop (𝓝 (finiteInteractionEnergy ρ eig hρ hρsum t p)))
    (hcontact : ∀ᶠ k in atTop, finiteInteractionEnergy ρ eig hρ hρsum (tk k) q + δ ≤ energy k)
    (htail : ∀ s ∈ Icc (0 : ℝ) 1, pathTail q s ≤ pathTail p s) : False := by
  have hq := ((continuous_finiteInteractionEnergy_temperature ρ eig hρ hρsum q).tendsto t).comp htk
  have hle := le_of_tendsto_of_tendsto (hq.add_const δ) henergy hcontact
  have hord := finiteInteractionEnergy_mono_tail ρ eig hρ hρsum ht p q htail
  linarith

end InvariantIsing

end

end OAI
