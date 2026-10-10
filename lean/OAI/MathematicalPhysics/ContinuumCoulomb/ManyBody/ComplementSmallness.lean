import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarScaleBudgets

namespace OAI

/-! Fixed exponent thresholds for the two smallness hypotheses in the
full-domain complement estimate. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_residual_complement_smallness {γ : ℝ} (hγ : 0 < γ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r k : ℕ, q+r ≤ k → ∀ N M : ℝ,
      2 ≤ N → 0 ≤ M → M ≤ N^r →
      M*((1/(N^k)^19)+(1/(N^k)^19)^2/(γ/4)) ≤ γ/8 := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_ratio_offset (1+4/γ) (by positivity : 0 < γ/8)
  refine ⟨q,hq,fun r k hk N M hN hM hMN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hR0 : 0 < N^k := by positivity
  have hR1 : 1 ≤ N^k := one_le_pow₀ (by linarith : 1 ≤ N)
  have h1 : M/(N^k)^19 ≤ N^r/(N^k)^2 := by
    gcongr
    decide
  have h2 : (4/γ)*M/(N^k)^38 ≤ (4/γ)*N^r/(N^k)^2 := by
    gcongr
    decide
  calc
    _ = M/(N^k)^19+(4/γ)*M/(N^k)^38 := by field_simp [ne_of_gt hγ]
    _ ≤ N^r/(N^k)^2+(4/γ)*N^r/(N^k)^2 := add_le_add h1 h2
    _ = (1+4/γ)*N^r/(N^k)^2 := by ring
    _ ≤ γ/8 := by simpa only [Nat.add_zero,pow_zero,div_one] using hbound r 0 k (by omega) N hN

theorem exists_nuclear_complement_smallness {a b B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r u k : ℕ, q+3*r+u ≤ k → ∀ N M A : ℝ,
      2 ≤ N → 0 ≤ M → M ≤ N^r → |A| ≤ N^u →
      0 < b/(2*N^(2*r)) ∧
      (B/(N^k)^20)*M+|A/(a*(N^k)^30)|+b/(2*N^(2*r)) ≤ b/N^(2*r) := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_ratio_offset (B+1/a) (by positivity : 0 < b/2)
  refine ⟨q,hq,fun r u k hk N M A hN hM hMN hA => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR0 : 0 < N^k := by positivity
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hr : N^r ≤ N^(r+u) := pow_le_pow_right₀ hN1 (by omega)
  have hu : N^u ≤ N^(r+u) := pow_le_pow_right₀ hN1 (by omega)
  have h1 : (B/(N^k)^20)*M ≤ B*N^(r+u)/(N^k)^2 := by
    calc
      _ = B*M/(N^k)^20 := by ring
      _ ≤ _ := by gcongr <;> first | exact hMN.trans hr | decide
  have h2 : |A/(a*(N^k)^30)| ≤ (1/a)*N^(r+u)/(N^k)^2 := by
    rw [abs_div,abs_of_pos (show 0 < a*(N^k)^30 by positivity)]
    calc
      _ = (1/a)*|A|/(N^k)^30 := by ring
      _ ≤ _ := by gcongr <;> first | exact hA.trans hu | decide
  have hsum : (B/(N^k)^20)*M+|A/(a*(N^k)^30)| ≤ (b/2)/N^(2*r) := by
    calc
      _ ≤ B*N^(r+u)/(N^k)^2+(1/a)*N^(r+u)/(N^k)^2 := add_le_add h1 h2
      _ = (B+1/a)*N^(r+u)/(N^k)^2 := by ring
      _ ≤ _ := hbound (r+u) (2*r) k (by omega) N hN
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ (b/2)/N^(2*r)+b/(2*N^(2*r)) := add_le_add hsum le_rfl
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
