import OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation
import OAI.NumberTheory.PiExponent.Jets.PolynomialJetPackets

namespace OAI

noncomputable section
namespace PiExponent.AlgebraicJetPackets

open MvPolynomial
variable {R : Type*} [CommRing R] {m : ℕ}

def triangularMap (c : Fin m → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R →ₐ[R] MvPolynomial (Fin (m+1)) R :=
  MvPolynomial.aeval (Fin.cases (1 + X 0)
    (fun i => C (c i) + X i.succ + Polynomial.aeval (X 0) (G i)))

def inverseTriangularMap (c : Fin m → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R →ₐ[R] MvPolynomial (Fin (m+1)) R :=
  MvPolynomial.aeval (Fin.cases (X 0 - 1)
    (fun i => X i.succ - C (c i) - Polynomial.aeval (X 0 - 1) (G i)))

@[simp] theorem triangularMap_X_zero (c : Fin m → R) (G : Fin m → Polynomial R) :
    triangularMap c G (X 0) = 1 + X 0 := by simp [triangularMap]

@[simp] theorem triangularMap_X_succ (c : Fin m → R) (G : Fin m → Polynomial R)
    (i : Fin m) :
    triangularMap c G (X i.succ) = C (c i) + X i.succ + Polynomial.aeval (X 0) (G i) := by
  simp [triangularMap]

@[simp] theorem inverseTriangularMap_X_zero (c : Fin m → R) (G : Fin m → Polynomial R) :
    inverseTriangularMap c G (X 0) = X 0 - 1 := by simp [inverseTriangularMap]

@[simp] theorem inverseTriangularMap_X_succ (c : Fin m → R) (G : Fin m → Polynomial R)
    (i : Fin m) :
    inverseTriangularMap c G (X i.succ) =
      X i.succ - C (c i) - Polynomial.aeval (X 0 - 1) (G i) := by
  simp [inverseTriangularMap]

theorem triangularMap_comp_inverse (c : Fin m → R) (G : Fin m → Polynomial R) :
    (triangularMap c G).comp (inverseTriangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X_succ, map_sub,
      triangularMap_X_succ, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      ← Polynomial.aeval_algHom_apply, triangularMap_X_zero, map_one, AlgHom.id_apply]
    rw [show (1 + X (0 : Fin (m+1)) - 1 : MvPolynomial (Fin (m+1)) R) = X 0 by ring]
    ring

theorem inverseTriangularMap_comp (c : Fin m → R) (G : Fin m → Polynomial R) :
    (inverseTriangularMap c G).comp (triangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [AlgHom.comp_apply, triangularMap_X_succ, map_add,
      inverseTriangularMap_X_succ, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      ← Polynomial.aeval_algHom_apply, inverseTriangularMap_X_zero, AlgHom.id_apply]
    ring

def triangularEquiv (c : Fin m → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R ≃ₐ[R] MvPolynomial (Fin (m+1)) R :=
  AlgEquiv.ofAlgHom (triangularMap c G) (inverseTriangularMap c G)
    (triangularMap_comp_inverse c G) (inverseTriangularMap_comp c G)

theorem liftSeries_polynomial (p : Polynomial R) :
    FormalLogJet.liftSeries m (p : PowerSeries R) =
      Polynomial.aeval (MvPowerSeries.X (0 : Fin (m+1))) p := by
  have h : (FormalLogJet.liftSeries (R := R) m).comp Polynomial.coeToPowerSeries.ringHom =
      (Polynomial.aeval (MvPowerSeries.X (0 : Fin (m+1)))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [MvPowerSeries.algebraMap_apply]
    · simp
  exact RingHom.congr_fun h p

theorem truncatedFormalJet_eq_polynomial (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : PiExponentApprox.FramePolynomial m) :
    FormalLogTruncation.truncatedFormalJet c T P =
      ((triangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P) :
        MvPowerSeries (Fin (m+1)) ℂ) := by
  have h : FormalLogTruncation.truncatedFormalJet c T =
      (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp
        (triangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp [FormalLogTruncation.truncatedFormalJet]
    | succ i =>
      simp only [FormalLogTruncation.truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_succ, AlgHom.comp_apply, triangularMap_X_succ, map_add]
      rw [liftSeries_polynomial, ← Polynomial.aeval_algHom_apply]
      simp [MvPowerSeries.algebraMap_apply]
  simpa using AlgHom.congr_fun h P

theorem truncatedFormalJet_inverse (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) :
    FormalLogTruncation.truncatedFormalJet c T
      (inverseTriangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P) =
      (P : MvPowerSeries (Fin (m+1)) ℂ) := by
  rw [truncatedFormalJet_eq_polynomial]
  have h := AlgHom.congr_fun
    (triangularMap_comp_inverse c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ))) P
  simpa using congrArg (fun Q : MvPolynomial (Fin (m+1)) ℂ =>
    (Q : MvPowerSeries (Fin (m+1)) ℂ)) h

theorem quotient_surjective_of_packet {A : Type*} [CommRing A] [Algebra R A]
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (f : A →ₐ[R] MvPowerSeries (Fin (m+1)) R)
    (hf : Function.Surjective (fun p => JetGeometry.rationalCoefficientPacket v H (f p))) :
    Function.Surjective ((Ideal.Quotient.mkₐ R (JetGeometry.rationalWeightedIdeal v hv H)).comp f) := by
  intro q
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨p, hp⟩ := hf (JetGeometry.rationalCoefficientPacket v H F)
  refine ⟨p, ?_⟩
  change Ideal.Quotient.mk _ (f p) = Ideal.Quotient.mk _ F
  apply Ideal.Quotient.eq.mpr
  exact (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv H _ _).mp hp

def algebraicJetMap (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ]
      MvPowerSeries (Fin (m+1)) ℂ ⧸ JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H :=
  (Ideal.Quotient.mkₐ ℂ (JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H)).comp
    (FormalLogTruncation.truncatedFormalJet c T)

def algebraicJetIdeal (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    Ideal (PiExponentApprox.FramePolynomial m) :=
  RingHom.ker (algebraicJetMap c T v hv H)

@[simp] theorem mem_algebraicJetIdeal (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (P : PiExponentApprox.FramePolynomial m) :
    P ∈ algebraicJetIdeal c T v hv H ↔
      FormalLogTruncation.truncatedFormalJet c T P ∈ JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H := by
  change Ideal.Quotient.mk _ _ = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

theorem truncatedFormalJet_packet_surjective (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogTruncation.truncatedFormalJet c T P)) := by
  intro packet
  obtain ⟨P, hP⟩ := PolynomialJetPackets.polynomial_packet_surjective v hv H packet
  refine ⟨inverseTriangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P, ?_⟩
  simpa only [truncatedFormalJet_inverse] using hP

theorem algebraicJetMap_surjective (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (algebraicJetMap c T v (fun i => (hv i).le) H) :=
  quotient_surjective_of_packet v (fun i => (hv i).le) H _
    (truncatedFormalJet_packet_surjective c T v hv H)

def algebraicJetQuotientEquiv (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    (PiExponentApprox.FramePolynomial m ⧸ algebraicJetIdeal c T v (fun i => (hv i).le) H) ≃ₐ[ℂ]
      (MvPowerSeries (Fin (m+1)) ℂ ⧸ JetGeometry.rationalWeightedIdeal (R := ℂ) v (fun i => (hv i).le) H) :=
  Ideal.quotientKerAlgEquivOfSurjective (algebraicJetMap_surjective c T v hv H)

@[simp] theorem algebraicJetQuotientEquiv_mk (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (P : PiExponentApprox.FramePolynomial m) :
    algebraicJetQuotientEquiv c T v hv H (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (FormalLogTruncation.truncatedFormalJet c T P) :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ P

theorem independent_truncatedFormalJet_packets_surjective {J : Type*}
    (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : J → PiExponentApprox.FramePolynomial m => fun j =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogTruncation.truncatedFormalJet (c j) T (P j))) := by
  intro packets
  choose P hP using fun j => truncatedFormalJet_packet_surjective (c j) T v hv H (packets j)
  exact ⟨P, funext hP⟩

theorem formalJet_packet_surjective (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogJet.formalJet c P)) := by
  let T : Fin m → ℕ := fun i => Nat.ceil (v i.succ / v 0)
  have hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0 := by
    intro i
    exact (div_le_iff₀ (hv 0)).mp (Nat.le_ceil _)
  have ht : Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      fun _ : Unit => JetGeometry.rationalCoefficientPacket v H
        (FormalLogTruncation.truncatedFormalJet c T P)) := by
    intro packets
    obtain ⟨P, hP⟩ := truncatedFormalJet_packet_surjective c T v hv H (packets ())
    refine ⟨P, ?_⟩
    funext j
    cases j
    exact hP
  have hs := (FormalLogTruncation.formalLog_packets_surjective_iff_truncated
    v (fun i => (hv i).le) H T hT (fun _ : Unit => c) (fun P => P)).mpr ht
  intro packet
  obtain ⟨P, hP⟩ := hs (fun _ => packet)
  exact ⟨P, congrFun hP ()⟩

end PiExponent.AlgebraicJetPackets

end

end OAI
