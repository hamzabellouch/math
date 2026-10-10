import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFiniteMeanFamily

namespace OAI

/-! Explicit polynomial majorants survive the read/restore operations in
an atlas. All dependence on transport constants stays in the profile. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open RealModes

def transportedMeanGeometry (L : ℕ) (G D E : ℕ → ℝ) (m : ℕ) : ℝ :=
  1+G m+D (m+L)+E m

lemma polynomialMeanProfile_transport_bound (p : ℕ) {C G D E A : ℝ}
    (hC : 0 ≤ C) (hG : 1 ≤ G) (hD : 1 ≤ D) (hE : 0 ≤ E) (hA : 1 ≤ A) :
    max 1 (E*(C*(G+max 1 (D*A))^p)*D) ≤
      (1+C)*(1+G+D+E+max 1 A)^(2*p+2) := by
  let u := 1+G+D+E+max 1 A
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hDA : 1 ≤ D*A := one_le_mul_of_one_le_of_one_le hD hA
  have hu : 1 ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hGD : G+D ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hDu : D ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hEu : E ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hAu : A ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hbase : G+max 1 (D*A) ≤ u^2 := by
    rw [max_eq_right hDA]
    calc
      G+D*A ≤ (G+D)*A := by nlinarith
      _ ≤ u*u := mul_le_mul hGD hAu hA0 (zero_le_one.trans hu)
      _ = u^2 := by ring
  have hp : (G+max 1 (D*A))^p ≤ (u^2)^p :=
    pow_le_pow_left₀ (by positivity) hbase p
  have hED : E*D ≤ u^2 := by
    simpa only [pow_two] using mul_le_mul hEu hDu hD0 (zero_le_one.trans hu)
  have hb : E*(C*(G+max 1 (D*A))^p)*D ≤ C*u^(2*p+2) := by
    calc
      _ = C*(E*D)*(G+max 1 (D*A))^p := by ring
      _ ≤ C*(u^2)*(u^2)^p := mul_le_mul
        (mul_le_mul_of_nonneg_left hED hC) hp (by positivity) (by positivity)
      _ = C*u^(2*p+2) := by rw [← pow_mul, mul_assoc, ← pow_add, Nat.add_comm 2 (2*p)]
  have hone : 1 ≤ u^(2*p+2) := one_le_pow₀ hu
  apply max_le
  · nlinarith [pow_nonneg (zero_le_one.trans hu) (2*p+2)]
  · exact hb.trans (by nlinarith [pow_nonneg (zero_le_one.trans hu) (2*p+2)])

lemma polynomialMeanProfile_value_transport_bound (p : ℕ) {C G D E A : ℝ}
    (hC : 0 ≤ C) (hG : 1 ≤ G) (hD : 1 ≤ D) (hE : 0 ≤ E) (hA : 1 ≤ A) :
    max 1 (E*(C*(G+max 1 (D*A))^p)) ≤
      (1+C)*(1+G+D+E+max 1 A)^(2*p+2) := by
  have h : E*(C*(G+max 1 (D*A))^p) ≤ E*(C*(G+max 1 (D*A))^p)*D := by
    exact le_mul_of_one_le_right (by positivity) hD
  exact (max_le_max_left 1 h).trans
    (polynomialMeanProfile_transport_bound p hC hG hD hE hA)

lemma transportedMeanGeometry_growth (L : ℕ) (G D E : ℕ → ℝ → ℝ)
    (hG : ∀ m, HasPolynomialBound (G m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hE : ∀ m, HasPolynomialBound (E m)) (m : ℕ) :
    HasPolynomialBound (fun x => transportedMeanGeometry L
      (fun r => G r x) (fun r => D r x) (fun r => E r x) m) :=
  (((polynomialBound_const zero_le_one).add (hG m)).add (hD (m+L))).add (hE m)

end ClosedSurfaceR4.PhaseMean

end

end OAI
