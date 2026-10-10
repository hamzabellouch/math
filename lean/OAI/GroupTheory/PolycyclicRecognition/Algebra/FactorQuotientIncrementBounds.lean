import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientChainDecay

namespace OAI

/-! # Summable bounds for the actual projected ray increments -/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- Polynomial Cartan coordinates and negative linear height turn the
compact-set contraction into the summable bound used for ray trajectories. -/
theorem factor_quotient_increment_polynomial_exp_bound
    {N D G Q V : Type*} [Group N] [Group D] [Group G] [Group Q]
    [SeminormedAddCommGroup V]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q)
    (log : Q → V) (size height : D → ℝ) (K : Set Q)
    {A rate B gap : ℝ} (hA : 0 ≤ A) (hrate : 0 < rate) (hB : 0 ≤ B) (hgap : 0 < gap)
    (p degree : ℕ)
    (hcontract : ∀ d, height d ≤ 0 → ∀ q ∈ K,
      ‖log (α d q)‖ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d))
    (n : ℕ) (x y : G) (u : N) (d : D) (hlift : ι u * κ d = x)
    (hsize0 : 0 ≤ size d) (hsize : size d ≤ B * (1 + (n : ℝ)) ^ degree)
    (hheight : height d ≤ -gap * n) (hstep : act (x⁻¹ * y) 1 ∈ K) :
    ‖log ((act x 1)⁻¹ * act y 1)‖ ≤
      (A * (1 + B) ^ p) * (1 + (n : ℝ)) ^ (degree * p) * Real.exp (-(rate * gap) * n) := by
  rw [factor_quotient_increment ι κ π α act hact x y u d hlift]
  have hneg : height d ≤ 0 := hheight.trans
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hgap.le) (Nat.cast_nonneg n))
  have hb : 1 + size d ≤ (1 + B) * (1 + (n : ℝ)) ^ degree := by
    have hp : 1 ≤ (1 + (n : ℝ)) ^ degree := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    nlinarith
  have hpoly : (1 + size d) ^ p ≤ (1 + B) ^ p * (1 + (n : ℝ)) ^ (degree * p) := by
    calc
      _ ≤ ((1 + B) * (1 + (n : ℝ)) ^ degree) ^ p := pow_le_pow_left₀ (by linarith) hb _
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hexp : Real.exp (rate * height d) ≤ Real.exp (-(rate * gap) * n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hheight hrate.le
    nlinarith
  calc
    _ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d) := hcontract d hneg _ hstep
    _ ≤ A * ((1 + B) ^ p * (1 + (n : ℝ)) ^ (degree * p)) *
        Real.exp (-(rate * gap) * n) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpoly hA) hexp
        (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
