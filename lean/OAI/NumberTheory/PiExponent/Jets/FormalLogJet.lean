import Mathlib
import OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame

namespace OAI

noncomputable section
namespace PiExponent.FormalLogJet
open MvPowerSeries
open PiExponent.FormalJetDerivatives

variable {R : Type*} [CommRing R]

def liftSeries (m : ℕ) : PowerSeries R →+* MvPowerSeries (Fin (m + 1)) R :=
  (finSuccEquiv R m).symm.toRingHom.comp (PowerSeries.map MvPowerSeries.C)

@[simp] theorem coeff_liftSeries (m : ℕ) (f : PowerSeries R)
    (d : Fin (m + 1) →₀ ℕ) :
    coeff d (liftSeries m f) = if d.tail = 0 then PowerSeries.coeff (d 0) f else 0 := by
  have h := coeff_coeff_finSuccEquiv (liftSeries m f) (k := d 0) (x := d.tail)
  rw [Finsupp.cons_tail] at h
  rw [← h]
  simp [liftSeries, PowerSeries.coeff_map, coeff_C]

@[simp] theorem liftSeries_X (m : ℕ) : liftSeries (R := R) m PowerSeries.X = X 0 := by
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

@[simp] theorem liftSeries_C (m : ℕ) (r : R) :
    liftSeries m (PowerSeries.C r) = C r := by
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

theorem pderiv_zero_liftSeries (m : ℕ) (f : PowerSeries R) :
    pderiv 0 (liftSeries m f) = liftSeries m (PowerSeries.derivative f) := by
  ext d
  rw [coeff_pderiv, coeff_liftSeries, coeff_liftSeries, PowerSeries.coeff_derivative]
  have ht : (d + Finsupp.single (0 : Fin (m+1)) 1).tail = d.tail := by
    ext i
    simp [Finsupp.tail_apply]
  simp only [ht, Finsupp.add_apply, Finsupp.single_eq_same]
  split_ifs <;> simp_all

theorem pderiv_succ_liftSeries (m : ℕ) (i : Fin m) (f : PowerSeries R) :
    pderiv i.succ (liftSeries m f) = 0 := by
  ext d
  rw [coeff_pderiv, coeff_liftSeries, coeff_zero]
  have ht : (d + Finsupp.single i.succ 1).tail ≠ 0 := by
    intro h
    have hi := DFunLike.congr_fun h i
    simp [Finsupp.tail_apply] at hi
  simp [ht]

def formalLog (m : ℕ) : MvPowerSeries (Fin (m+1)) ℂ :=
  liftSeries m (PowerSeries.log ℂ)

@[simp] theorem pderiv_succ_formalLog (m : ℕ) (i : Fin m) :
    pderiv i.succ (formalLog m) = 0 := pderiv_succ_liftSeries m i _

theorem one_add_X_mul_pderiv_formalLog (m : ℕ) :
    (1 + X 0) * pderiv 0 (formalLog m) = 1 := by
  have h := congrArg (liftSeries m) (PowerSeries.derivative_log_mul_one_add_X (A := ℂ))
  rw [map_mul, map_add, map_one, liftSeries_X] at h
  rw [formalLog, pderiv_zero_liftSeries, mul_comm]
  exact h

def formalJet {m : ℕ} (c : Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + X 0)
    (fun i => C (c i) + X i.succ + formalLog m))

@[simp] theorem formalJet_Y {m : ℕ} (c : Fin m → ℂ) :
    formalJet c (MvPolynomial.X (0 : Fin (m+1))) = 1 + X 0 := by
  simp [formalJet]

@[simp] theorem formalJet_X {m : ℕ} (c : Fin m → ℂ) (i : Fin m) :
    formalJet c (MvPolynomial.X i.succ) = C (c i) + X i.succ + formalLog m := by
  simp [formalJet]

theorem derivation_map_of_X {σ S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPolynomial σ R →ₐ[R] S)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (δ : Derivation R S S)
    (hX : ∀ i, φ (D (MvPolynomial.X i)) = δ (φ (MvPolynomial.X i)))
    (p : MvPolynomial σ R) : φ (D p) = δ (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

theorem formalJet_frame_X {m : ℕ} (c : Fin m → ℂ) (i j : Fin (m+1)) :
    formalJet c (PiExponentApprox.polynomialFrame m i (MvPolynomial.X j)) =
      jetFrame m i (formalJet c (MvPolynomial.X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [PiExponentApprox.polynomialFrame_zero,
        PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X]
    | succ j =>
      simp [PiExponentApprox.polynomialFrame_zero,
        PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X,
        Pi.single_apply, MvPowerSeries.pderiv_X_of_ne,
        one_add_X_mul_pderiv_formalLog]
  | succ i =>
    rw [PiExponentApprox.polynomialFrame_pos m i.succ (Fin.succ_ne_zero i),
      jetFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp [MvPowerSeries.pderiv_X_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    | succ j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_polynomialFrame {m : ℕ} (c : Fin m → ℂ)
    (i : Fin (m+1)) (p : PiExponentApprox.FramePolynomial m) :
    formalJet c (PiExponentApprox.polynomialFrame m i p) =
      jetFrame m i (formalJet c p) :=
  derivation_map_of_X (formalJet c) (PiExponentApprox.polynomialFrame m i)
    (jetFrame m i) (formalJet_frame_X c i) p

theorem formalJet_polynomialFrameWord {m : ℕ} (c : Fin m → ℂ)
    (word : List (Fin (m+1))) (p : PiExponentApprox.FramePolynomial m) :
    formalJet c (PiExponentApprox.polynomialFrameWord m word p) =
      jetFrameWord m word (formalJet c p) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    rw [PiExponentApprox.polynomialFrameWord_cons, formalJet_polynomialFrame, ih]
    rfl

theorem formalJet_polynomialFrameWord_vanishing {m : ℕ} (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin (m+1))) :
    formalJet c (PiExponentApprox.polynomialFrameWord m word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  rw [formalJet_polynomialFrameWord]
  exact jetFrameWord_mem_rationalWeightedIdeal v hv H (formalJet c p) hp word

end PiExponent.FormalLogJet

end

end OAI
