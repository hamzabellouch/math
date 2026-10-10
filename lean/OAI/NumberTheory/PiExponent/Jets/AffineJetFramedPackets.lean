import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface
import OAI.NumberTheory.PiExponent.Jets.AffineJetPackets

namespace OAI

noncomputable section
namespace PiExponent.AffineJetFramedPackets
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealPullback
open PiExponent.AffineJetCoefficientInterface PiExponent.BlowupJetSurjectivity
variable {X : Scheme} {m : ℕ} {J : Type} [Fintype J]

theorem surjective_of_jetRestriction
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (j : Spec (CommRingCat.of (PiExponentApprox.FramePolynomial m)) ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (A : LineBundle X) (frame : Frame j A)
    (hI : I.comap j = specIdeal (CompactLogJetIdeal.polynomialIdeal c T e))
    (hs : ((I^n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : Sections A n => fun k =>
      JetGeometry.rationalCoefficientPacket v (n * R)
        (FormalLogJet.formalJet (c k) (coefficient j A n frame s))) := by
  apply AffineJetPackets.packets_surjective_of_polynomialIdeal_quotient c hc T e hepos
    v hv hT R he n (coefficient j A n frame)
  exact AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    I A n j frame (CompactLogJetIdeal.polynomialIdeal c T e) hI hs hjet

end PiExponent.AffineJetFramedPackets
end

end OAI
