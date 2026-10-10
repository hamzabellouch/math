import OAI.NumberTheory.PiExponent.Jets.FormalJetIndices
import OAI.NumberTheory.PiExponent.Jets.JetGeometry

namespace OAI

noncomputable section
namespace PiExponent.PolynomialJetPackets
open MvPowerSeries JetGeometry

theorem polynomial_packet_surjective {R : Type*} [CommRing R] {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun p : MvPolynomial (Fin n) R =>
      rationalCoefficientPacket v H (p : MvPowerSeries (Fin n) R)) := by
  classical
  let I := {d : Fin n →₀ ℕ // Finsupp.weight v d < H}
  let : Fintype I := Fintype.ofEquiv _ (FormalMatrixBridge.rationalJetIndexEquiv v hv H).symm
  intro packet
  change I → R at packet
  let p : MvPolynomial (Fin n) R := ∑ d : I, MvPolynomial.monomial d.val (packet d)
  refine ⟨p, ?_⟩
  funext d
  change coeff d.val (p : MvPowerSeries (Fin n) R) = packet d
  simp only [p, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, Subtype.val_inj]
  change (∑ x : I, if x = (d : I) then packet x else 0) = packet d
  exact Fintype.sum_ite_eq' (d : I) packet

theorem polynomial_packets_surjective {R J : Type*} [CommRing R] {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun p : J → MvPolynomial (Fin n) R =>
      fun j => rationalCoefficientPacket v H (p j : MvPowerSeries (Fin n) R)) := by
  intro packets
  choose p hp using fun j => polynomial_packet_surjective v hv H (packets j)
  exact ⟨p, funext hp⟩

end PiExponent.PolynomialJetPackets

end

end OAI
