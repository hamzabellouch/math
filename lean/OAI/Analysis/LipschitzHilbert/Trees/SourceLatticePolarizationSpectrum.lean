import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarization
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeSpectrum

namespace OAI

/-! Polarization preserves the original physical packet spectrum.
Both profiles use the same carrier and geometry, so their linear
combination has no Fourier support outside their shared wedge and band. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem physicalPlanarPacket_add_smul (f g : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (a b l W θ frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    physicalPlanarPacket (f + c • g) a b l W θ frequency hl hW =
      physicalPlanarPacket f a b l W θ frequency hl hW +
        c • physicalPlanarPacket g a b l W θ frequency hl hW := by
  ext z
  simp only [physicalPlanarPacket_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem planarFourier_add (f g : SchwartzMap (ℝ × ℝ) ℂ) (frequency : ℝ × ℝ) :
    planarFourier (f + g : SchwartzMap (ℝ × ℝ) ℂ) frequency =
      planarFourier f frequency + planarFourier g frequency := by
  unfold planarFourier
  simp only [add_apply, smul_add]
  exact integral_add (planarFourier_integrand_integrable f frequency)
    (planarFourier_integrand_integrable g frequency)

theorem planarAngularFourier_add_smul (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (frequency : ℝ × ℝ) :
    planarAngularFourier (f + c • g : SchwartzMap (ℝ × ℝ) ℂ) frequency =
      planarAngularFourier f frequency + c * planarAngularFourier g frequency := by
  unfold planarAngularFourier
  rw [planarFourier_add, planarFourier_smul]

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)

theorem polarize_physicalPacket (c : ℂ) (hc : ‖c‖ = 1)
    (t : ℝ) (j : Fin N) (u : ι j) (k : κ) :
    (P.polarize alt hAlt c hc).physicalPacket t j u k =
      P.physicalPacket t j u k + c • (P.withProfile alt hAlt).physicalPacket t j u k := by
  change physicalPlanarPacket (P.profile j u k + c • alt j u k)
      (P.actualX j u) (P.actualZ j u + t * P.actualX j u)
      (P.length j) P.width (t + P.rowSlope j) (P.frequency k)
      (P.length_pos j).ne' P.width_pos.ne' = _
  exact physicalPlanarPacket_add_smul (P.profile j u k) (alt j u k) c
    (P.actualX j u) (P.actualZ j u + t * P.actualX j u)
    (P.length j) P.width (t + P.rowSlope j) (P.frequency k)
    (P.length_pos j).ne' P.width_pos.ne'

theorem polarize_physicalFourier (c : ℂ) (hc : ‖c‖ = 1)
    (t : ℝ) (j : Fin N) (u : ι j) (k : κ) (ξ η : ℝ) :
    planarAngularFourier ((P.polarize alt hAlt c hc).physicalPacket t j u k) (ξ, η) =
      planarAngularFourier (P.physicalPacket t j u k) (ξ, η) +
        c * planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j u k) (ξ, η) := by
  rw [P.polarize_physicalPacket alt hAlt c hc, planarAngularFourier_add_smul]

/-- Every zero shared by the two original physical spectra is retained. -/
theorem polarize_physicalFourier_eq_zero (c : ℂ) (hc : ‖c‖ = 1)
    (t : ℝ) (j : Fin N) (u : ι j) (k : κ) (ξ η : ℝ)
    (hp : planarAngularFourier (P.physicalPacket t j u k) (ξ, η) = 0)
    (hq : planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j u k) (ξ, η) = 0) :
    planarAngularFourier ((P.polarize alt hAlt c hc).physicalPacket t j u k) (ξ, η) = 0 := by
  rw [P.polarize_physicalFourier alt hAlt c hc, hp, hq, mul_zero, add_zero]

/-- The original wedge and positive vertical band are sufficient for
all four polarization families; no additional support hypothesis is used. -/
theorem polarize_spectrum (c : ℂ) (hc : ‖c‖ = 1)
    (t w cStar cEta CEta : ℝ)
    (hp : ∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ, η) ≠ 0 →
      |ξ + (t + P.rowSlope j) * η| ≤ cStar / P.length j ∧
        cEta ≤ w * η ∧ w * η ≤ CEta)
    (hq : ∀ j u k ξ η,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j u k) (ξ, η) ≠ 0 →
      |ξ + (t + P.rowSlope j) * η| ≤ cStar / P.length j ∧
        cEta ≤ w * η ∧ w * η ≤ CEta) :
    ∀ j u k ξ η,
      planarAngularFourier ((P.polarize alt hAlt c hc).physicalPacket t j u k) (ξ, η) ≠ 0 →
      |ξ + (t + P.rowSlope j) * η| ≤ cStar / P.length j ∧
        cEta ≤ w * η ∧ w * η ≤ CEta := by
  intro j u k ξ η hnonzero
  by_cases hzero : planarAngularFourier (P.physicalPacket t j u k) (ξ, η) = 0
  · apply hq j u k ξ η
    intro hzero'
    exact hnonzero (P.polarize_physicalFourier_eq_zero alt hAlt c hc t j u k ξ η hzero hzero')
  · exact hp j u k ξ η hzero

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
