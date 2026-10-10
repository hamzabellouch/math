import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GroundRoundingInterval
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarScaleBudgets

namespace OAI

/-! A polynomial coordinate precision controls the full Coulomb ground
energy, including the total charge of the large finite nuclear grid. -/

noncomputable section
namespace ContinuumCoulomb

theorem inverse_power_product_le {N : ℝ} (hN : 1 ≤ N)
    {a b p : ℕ} (hab : b+p ≤ a) : (N^a)⁻¹*N^b ≤ (N^p)⁻¹ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [inv_mul_eq_div,inv_eq_one_div,div_le_div_iff₀ (by positivity) (by positivity),one_mul,← pow_add]
  exact pow_le_pow_right₀ hN (by omega)

theorem rounding_polynomial_budget {N Q M δ E : ℝ} (hN : 2 ≤ N)
    {r q c p a : ℕ} (ha : c+3*q+r+p+8 ≤ a)
    (hQ : 0 ≤ Q) (hQN : Q ≤ N^q) (_hM : 0 ≤ M) (hMN : M ≤ N^r)
    (hE : E ≤ N^c) (hδ : 0 ≤ δ) (hδN : δ ≤ (N^a)⁻¹) :
    32*δ*Q ≤ 1 ∧ 32*δ*Q*(E+4*M*Q^2) ≤ (N^p)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  let b := c+r+3*q
  have hMQ : M*Q^2 ≤ N^(r+2*q) := by
    calc
      _ ≤ N^r*(N^q)^2 := mul_le_mul hMN (pow_le_pow_left₀ hQ hQN 2) (sq_nonneg Q) (by positivity)
      _ = _ := by rw [show 2*q=q*2 by omega,pow_add,pow_mul]
  have hterms : E+4*M*Q^2 ≤ 5*N^(c+r+2*q) := by
    have hEc := hE.trans (pow_le_pow_right₀ hN1 (by omega : c ≤ c+r+2*q))
    have hMc := hMQ.trans (pow_le_pow_right₀ hN1 (by omega : r+2*q ≤ c+r+2*q))
    linarith only [hEc,hMc]
  have hnum : 32*Q*(E+4*M*Q^2) ≤ 160*N^b := by
    calc
      _ ≤ 32*Q*(5*N^(c+r+2*q)) := mul_le_mul_of_nonneg_left hterms (by positivity)
      _ ≤ 32*N^q*(5*N^(c+r+2*q)) := by gcongr
      _ = _ := by dsimp [b]; rw [pow_add,pow_add,pow_add]; ring
  have h160 : (160:ℝ) ≤ N^8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 8
    norm_num at hh
    linarith
  have hnum' : 160*N^b ≤ N^(b+8) := by
    rw [pow_add N b 8]
    nlinarith [pow_nonneg hN0.le b]
  constructor
  · have h32 : 32*Q ≤ N^(b+8) := by
      have hQb : Q ≤ N^b := hQN.trans (pow_le_pow_right₀ hN1 (by dsimp [b]; omega))
      have h32' : (32:ℝ) ≤ N^8 := (by norm_num : (32:ℝ) ≤ 160).trans h160
      rw [pow_add N b 8]
      nlinarith [mul_le_mul h32' hQb hQ (pow_nonneg hN0.le 8)]
    calc
      _ = δ*(32*Q) := by ring
      _ ≤ (N^a)⁻¹*N^(b+8) := mul_le_mul hδN h32 (by positivity) (by positivity)
      _ ≤ 1 := by simpa only [pow_zero,inv_one] using inverse_power_product_le hN1 (a := a) (b := b+8) (p := 0) (by dsimp [b]; omega)
  · calc
      _ = δ*(32*Q*(E+4*M*Q^2)) := by ring
      _ ≤ δ*(160*N^b) := mul_le_mul_of_nonneg_left hnum hδ
      _ ≤ (N^a)⁻¹*N^(b+8) := mul_le_mul hδN hnum' (by positivity) (by positivity)
      _ ≤ _ := inverse_power_product_le hN1 (by dsimp [b]; omega)

end ContinuumCoulomb

end

end OAI
