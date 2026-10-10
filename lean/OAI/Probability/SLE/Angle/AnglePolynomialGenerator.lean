import OAI.Probability.SLE.Angle.CanonicalAngleSemigroup

namespace OAI

/-! The cosine-coordinate generator in the actual logarithmic radius
clock. Its polynomial eigenvalues retain the paper's time normalization. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def anglePolynomialGenerator (κ : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C (κ/8)*(1-X^2)*p.derivative.derivative - C (1+κ/8)*X*p.derivative

def anglePolynomialEigenvalue (κ : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)+(κ/8)*(n:ℝ)^2

lemma anglePolynomialGenerator_add (κ : ℝ) (p q : ℝ[X]) :
    anglePolynomialGenerator κ (p+q)=
      anglePolynomialGenerator κ p+anglePolynomialGenerator κ q := by
  simp only [anglePolynomialGenerator,map_add]
  ring

lemma anglePolynomialGenerator_C_mul (κ c : ℝ) (p : ℝ[X]) :
    anglePolynomialGenerator κ (C c*p)=C c*anglePolynomialGenerator κ p := by
  simp only [anglePolynomialGenerator,derivative_C_mul]
  ring

lemma anglePolynomialGenerator_one (κ : ℝ) : anglePolynomialGenerator κ 1=0 := by
  simp [anglePolynomialGenerator]

lemma anglePolynomialGenerator_X (κ : ℝ) :
    anglePolynomialGenerator κ X = -C (anglePolynomialEigenvalue κ 1)*X := by
  simp only [anglePolynomialGenerator,anglePolynomialEigenvalue,derivative_X,
    derivative_one,mul_zero,Nat.cast_one,one_pow,add_comm (1:ℝ),
    map_add,map_one]
  ring_nf

lemma anglePolynomialGenerator_X_pow_add_two (κ : ℝ) (n : ℕ) :
    anglePolynomialGenerator κ (X^(n+2)) =
      C ((κ/8)*((n:ℝ)+2)*((n:ℝ)+1))*X^n -
        C (anglePolynomialEigenvalue κ (n+2))*X^(n+2) := by
  simp only [anglePolynomialGenerator,derivative_X_pow,derivative_C_mul,
    show n+2-1=n+1 by omega,show n+1-1=n by omega]
  simp only [anglePolynomialEigenvalue,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  simp only [pow_add,pow_one]
  simp only [map_add,map_mul,map_pow,map_ofNat,map_one]
  ring

lemma anglePolynomialEigenvalue_strictMono {κ : ℝ} (hκ : 0<κ) :
    StrictMono (anglePolynomialEigenvalue κ) := by
  intro n m hnm
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hnm' : (n:ℝ) < m := Nat.cast_lt.mpr hnm
  have hsq : (n:ℝ)^2<(m:ℝ)^2 := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hsq (by positivity : 0<κ/8)
  unfold anglePolynomialEigenvalue
  linarith

lemma anglePolynomialEigenvalue_clock (κ : ℝ) (hκ : κ≠0) (n : ℕ) :
    anglePolynomialEigenvalue κ n=(κ/4)*((n:ℝ)*((n:ℝ)+4*Target.a κ)/2) := by
  unfold anglePolynomialEigenvalue Target.a
  field_simp
  ring

end SLEExactGauge

end

end OAI
