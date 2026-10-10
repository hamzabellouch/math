import OAI.Dynamics.ConditionalShuffle.OverlayGauge

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Overlay
open Thorp Thorp.Conditional Revealed.Split Revealed.Instrument Revealed.Scheduled

lemma fairMass_equiv_tv {Ω G : Type} [Fintype Ω] [Fintype G] (f : Ω → G) (e : G ≃ G) :
    tv (fairMass (fun ω => e (f ω))) (fun _ => (Fintype.card G : ℝ)⁻¹) =
      tv (fairMass f) (fun _ => (Fintype.card G : ℝ)⁻¹) := by
  unfold tv
  rw [← Equiv.sum_comp e]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  simp only [fairMass, e.injective.eq_iff]

variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]

lemma expectedTV_instrument (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool) (t : ℕ) :
    expectedTV d L σ t = Instrument.distance (stepInstrument (d+1) σ) (0,Split.outside L) t := by
  unfold expectedTV conditionalLaw
  have hh (c : History (d+1) t) :
      tv (fairMass (overlayRun d L σ t c)) (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) =
        tv (fairMass (resampledRun (stepInstrument (d+1) σ) (xorIncrement d σ) (0,Split.outside L) t c))
          (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) := by
    have he : overlayRun d L σ t c = fun r =>
        ((Equiv.mulLeft ((assignment (L.trans (run (d+1) t c)))⁻¹)).trans
          (Equiv.mulRight (assignment L)))
            (resampledRun (stepInstrument (d+1) σ) (xorIncrement d σ) (0,Split.outside L) t c r) := by
      funext r
      exact overlayRun_gauge d L σ t c r
    rw [he]
    exact fairMass_equiv_tv _ _
  simp_rw [hh]
  exact resampled_distance (stepInstrument (d+1) σ) (xorIncrement d σ) (xorIncrement_law d σ) _ t

end Revealed.Overlay

end

end OAI
