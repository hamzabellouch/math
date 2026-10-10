import OAI.MeasureTheory.Falconer.Estimates.FarError

namespace OAI

/-! # Fixed truncation orders and arbitrary-power far remainders -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem exists_far_truncation_orders (m : ℕ) {σ loss : ℝ}
    (hσ : 0 < σ) : ∃ M q : ℕ, 1 ≤ M ∧
      loss ≤ (16*σ)*(((m+2:ℕ):ℝ)/2+(q:ℝ)) ∧
      -(16*σ)*(M:ℝ)+2*(m+3) ≤ -loss := by
  obtain ⟨j,hj⟩ := exists_nat_ge ((loss+2*(m+3))/(16*σ))
  obtain ⟨q,hq⟩ := exists_nat_ge (loss/(16*σ))
  have hj' := (div_le_iff₀ (by positivity : 0 < 16*σ)).mp hj
  have hq' := (div_le_iff₀ (by positivity : 0 < 16*σ)).mp hq
  refine ⟨j+1,q,by omega,?_,?_⟩
  · have hm : 0 ≤ (16*σ)*((m+2:ℕ):ℝ)/2 := by positivity
    nlinarith
  · push_cast
    nlinarith

 theorem eventual_far_error_absorbed (m K : ℕ) {B Cerr ε : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ Cerr) (hε : 0 < ε) (T : ℝ) :
    ∃ N₀ : ℕ, ∀ (D : JetStateFarData m B), N₀ ≤ D.N → 1 ≤ D.Z →
      T+5*((m+3:ℕ):ℝ)+ε ≤ D.loss →
      D.farError K Cerr ≤ ENNReal.ofReal (((2:ℝ)^D.N)^(-T)) := by
  obtain ⟨N₁,hpoly⟩ := PlanarFalconer.fixed_polynomial_subpower 1 (half_pos hε)
  obtain ⟨N₂,hconst⟩ := Regularization.fixed_constant_absorbed (half_pos hε)
    (Cerr*(B^K)^4)
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro D hN hZ hloss
  have hNpos : 1 ≤ D.N := (le_max_left _ _).trans hN
  have hp := hpoly D.N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hc := hconst D.N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hR : 1 ≤ (2:ℝ)^D.N := D.base_one
  have hRp : 0 < (2:ℝ)^D.N := by positivity
  have hpoly' : ((D.N+3:ℕ):ℝ) ≤ ((2:ℝ)^D.N)^(ε/2) := by
    apply (show ((D.N+3:ℕ):ℝ) ≤ 4*(D.N:ℝ)+1 from ?_).trans
      (by simpa only [pow_one] using hp)
    push_cast
    have hn : (1:ℝ) ≤ D.N := by exact_mod_cast hNpos
    linarith
  have hcoeff : ((D.N+3:ℕ):ℝ)*Cerr*(B^K)^4 ≤ ((2:ℝ)^D.N)^ε := by
    calc
      _ = ((D.N+3:ℕ):ℝ)*(Cerr*(B^K)^4) := by ring
      _ ≤ ((2:ℝ)^D.N)^(ε/2)*((2:ℝ)^D.N)^(ε/2) :=
        mul_le_mul hpoly' hc (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hRp]; congr 1; ring
  have hz : D.Z⁻¹ ≤ 1 := (inv_le_one₀ D.Z_pos).mpr hZ
  have hb : (B^K*D.Z⁻¹)^4 ≤ (B^K)^4 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz
      (pow_nonneg (zero_le_one.trans hB) K)
  apply (D.farError_bound K hC).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((D.N+3:ℕ):ℝ)*Cerr*(B^K)^4 *
        ((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ)-D.loss) := by gcongr
    _ ≤ ((2:ℝ)^D.N)^ε*((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ)-D.loss) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = ((2:ℝ)^D.N)^(ε+5*((m+3:ℕ):ℝ)-D.loss) := by
      rw [← Real.rpow_add hRp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by linarith)

end Falconer

end OAI
