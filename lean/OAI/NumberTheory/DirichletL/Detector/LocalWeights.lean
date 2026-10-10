import OAI.NumberTheory.DirichletL.Detector.PrimeConstants
import OAI.NumberTheory.DirichletL.Detector.PhasePowers

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma even_diagonal_exponent (r : ℕ) : r + (2*r).choose 2 = 2*r*r := by
  rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  cases r with
  | zero => simp
  | succ r =>
    rw [show 2*(r+1)-1 = 2*r+1 by omega]
    ring

def localCubePhase (C omega : ℂ) (e l k : ℕ) : ℂ :=
  C^l * omega^((e+3*l)*k+e*l+l.choose 2)

theorem localCubePhase_even (C omega : ℂ) (hC : C^2=omega) (ho : omega^2=1)
    (e r k : ℕ) : localCubePhase C omega e (2*r) k = omega^(e*k) := by
  unfold localCubePhase
  rw [pow_mul C 2 r, hC, ← pow_add]
  have he : r+((e+3*(2*r))*k+e*(2*r)+(2*r).choose 2) =
      e*k+2*(3*r*k+e*r+r*r) := by
    have hd := even_diagonal_exponent r
    nlinarith
  rw [he, pow_add, pow_mul omega 2, ho, one_pow, mul_one]

def weightedScalar (Q eta a G1 C omega X W V scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (-eta*X/G1)^e * (a*X^3/Q)^l * localCubePhase C omega e l k * scalar * W^k * V^m

lemma weightedScalar_zero (Q eta a G1 C omega X W V : ℂ) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V 0 e l k m = 0 := by
  simp [weightedScalar]

def evenRatio (Q a X V : ℂ) : ℂ := a^2*Q^4*X^6*V

lemma weighted_squarefree_boundary (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r)*G1) 1 (2*r) 0 r =
      evenRatio Q a X V ^ r * (-eta*X) := by
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [mul_zero, pow_zero, pow_one, mul_one]
  unfold evenRatio
  rw [mul_pow, mul_pow, mul_pow, div_pow, mul_pow, pow_mul, pow_mul, pow_mul, pow_mul]
  field_simp
  ring

lemma weighted_even_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+5)*(Q-1))
      0 (2*r+2) 0 (r+1+d) =
      evenRatio Q a X V ^ r * (evenRatio Q a X V*(1-Q⁻¹)*V^d) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [zero_mul, pow_zero, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_even_kone (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+6))
      0 (2*r+2) 1 (r+1) = evenRatio Q a X V ^ r * (W*evenRatio Q a X V) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [pow_zero, pow_one, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_squarefree_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V
      ((omega⁻¹*G1)*(Q^(6*r)*(Q-1))) 1 (2*r) 1 (r+1+d) =
      evenRatio Q a X V ^ r * (-eta*(Q-1)*X*W*V^(d+1)) := by
  have hω : omega ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at ho; norm_num at ho
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [one_mul, pow_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI
