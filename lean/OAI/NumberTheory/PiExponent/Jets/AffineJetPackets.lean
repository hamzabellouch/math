import Mathlib.RingTheory.Ideal.Quotient.Operations
import OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal
import OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime

namespace OAI

noncomputable section
namespace PiExponent.AffineJetPackets
open CompactJetPolynomial
open scoped BigOperators

variable {m : ℕ}

theorem formalJet_packet_eq_of_sub_mem_pow
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P Q : PiExponentApprox.FramePolynomial m)
    (hPQ : P - Q ∈ powerIdeal c (logPolynomials T) e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet c P) =
      JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet c Q) := by
  apply (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv (n * R) _ _).mpr
  simpa only [map_sub] using formalJet_mem_weighted_of_mem_pow c T e v hv hT R he n
    (P - Q) hPQ

theorem formalJet_packets_surjective {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m => fun j =>
      JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet (c j) P)) := by
  classical
  intro packets
  choose P hP using fun j => AlgebraicJetPackets.formalJet_packet_surjective (c j)
    v hv (n * R) (packets j)
  have hcop := JetPowerIdealCoprime.powerIdeal_pow_pairwise_isCoprime c hc
    (logPolynomials T) (logPolynomials_eval_zero T) e hepos n
  obtain ⟨Q, hQ⟩ := Ideal.exists_forall_sub_mem_ideal hcop P
  refine ⟨Q, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow (c j) T e v (fun i => (hv i).le)
    hT R he n Q (P j) (hQ j)).trans (hP j)

theorem packets_surjective_of_polynomialIdeal_quotient {α J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → PiExponentApprox.FramePolynomial m)
    (hf : Function.Surjective (fun a =>
      Ideal.Quotient.mk (CompactLogJetIdeal.polynomialIdeal c T e ^ n) (f a))) :
    Function.Surjective (fun a j =>
      JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet (c j) (f a))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJet_packets_surjective c hc T e hepos v hv hT R he n packets
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ P)
  have hdiff : f a - P ∈ CompactLogJetIdeal.polynomialIdeal c T e ^ n :=
    Ideal.Quotient.eq.mp ha
  refine ⟨a, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow (c j) T e v (fun i => (hv i).le)
    hT R he n (f a) P (CompactLogJetIdeal.polynomialIdeal_pow_le c T e n j hdiff)).trans
      (congrFun hP j)

end PiExponent.AffineJetPackets

end

end OAI
