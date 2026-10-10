import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedLattice
import OAI.Analysis.LipschitzHilbert.Phase.PlanarSliceFourierAngular

namespace OAI

/-! Passing to a reference direction is an exact shear of the original
packets. The Fourier wedge and vertical bin are transported exactly. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem planarAngularFourier_slopeShear (f : ℝ×ℝ → ℂ) (t xi eta : ℝ) :
    planarAngularFourier (fun z => f (slopeShear t z)) (xi,eta)=
      planarAngularFourier f (xi-t*eta,eta) := by
  rw [planarAngularFourier_eq_integral,planarAngularFourier_eq_integral]
  have h := (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding
    (fun z : ℝ×ℝ => Complex.exp (-(Complex.I*(z.1*(xi-t*eta,eta).1+
      z.2*(xi-t*eta,eta).2)))*f z)
  refine Eq.trans ?_ h
  apply integral_congr_ae
  filter_upwards [] with z
  congr 2
  change -(Complex.I*((z.1:ℂ)*(xi:ℂ)+(z.2:ℂ)*(eta:ℂ)))=
    -(Complex.I*((z.1:ℂ)*((xi-t*eta:ℝ):ℂ)+((z.2+t*z.1:ℝ):ℂ)*(eta:ℂ)))
  push_cast
  ring

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalPacket_slopeShear (t : ℝ) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (z : ℝ×ℝ) :
    P.physicalPacket t j l u k (slopeShear t z)=P.physicalPacket 0 j l u k z := by
  simp only [physicalPacket,physicalPlanarPacket_apply,zero_mul,add_zero,zero_add]
  change Complex.exp (((P.frequency k*
      ((z.2+t*z.1-(P.actualZ j l u+t*P.actualX j l u))-
        (t+P.rowSlope j l)*(z.1-P.actualX j l u))):ℝ)*Complex.I)*
    P.profile j l u k ((z.1-P.actualX j l u)/P.length j,
      ((z.2+t*z.1-(P.actualZ j l u+t*P.actualX j l u))-
        (t+P.rowSlope j l)*(z.1-P.actualX j l u))/P.width)=_
  have he : (z.2+t*z.1-(P.actualZ j l u+t*P.actualX j l u))-
      (t+P.rowSlope j l)*(z.1-P.actualX j l u)=
      (z.2-P.actualZ j l u)-P.rowSlope j l*(z.1-P.actualX j l u) := by ring
  rw [he]

theorem physicalPacket_shear_fourier (t : ℝ) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (xi eta : ℝ) :
    planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)=
      planarAngularFourier (P.physicalPacket t j l u k) (xi-t*eta,eta) := by
  have he : (P.physicalPacket 0 j l u k : ℝ×ℝ → ℂ)=
      fun z => P.physicalPacket t j l u k (slopeShear t z) := by
    funext z
    exact (P.physicalPacket_slopeShear t j l u k z).symm
  rw [he,planarAngularFourier_slopeShear]

theorem reference_packet_spectrum (t w cStar cEta CEta : ℝ)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta)≠0 →
      |xi+(t+P.rowSlope j l)*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta := by
  intro j l u k xi eta hn
  rw [P.physicalPacket_shear_fourier t] at hn
  have h := hspectrum j l u k (xi-t*eta) eta hn
  have he : xi-t*eta+(t+P.rowSlope j l)*eta=xi+P.rowSlope j l*eta := by ring
  simpa only [he] using h

theorem reference_packet_bin (t Cv : ℝ)
    (hbin : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta)≠0 →
      |eta-P.frequency k|≤Cv/P.width) :
    ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |eta-P.frequency k|≤Cv/P.width := by
  intro j l u k xi eta hn
  rw [P.physicalPacket_shear_fourier t] at hn
  exact hbin j l u k (xi-t*eta) eta hn

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
