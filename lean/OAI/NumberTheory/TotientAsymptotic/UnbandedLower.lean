import OAI.NumberTheory.TotientAsymptotic.RegionLower
import OAI.NumberTheory.TotientAsymptotic.TailRenewal

namespace OAI

/-! Uniform scaled lower coordinates for the unbanded witness regions. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The first retained tail prime forces every continuous prefix coordinate
above a fixed multiple of `H rho^(-h)`. This is the lower bound needed when
thickening tail boxes after removing the prefix bands. -/
theorem tailPrefixRegion_scaled_lower (hford : FordRenewalInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ {x s : ℝ} {H : ℕ} {η : TailDatum H},
      0 ≤ s → IsWitness H s η → P H < H → H ≤ m x →
      ∀ {u : Fin (R x H) → ℝ}, u ∈ tailPrefixRegion x H η →
      ∀ i, c*(H-1 : ℕ) ≤ rho^(m x-(i.val+1))*u i := by
  obtain ⟨c, hc, hg⟩ := renewal_uniform_lower hford
  refine ⟨(9/10 : ℝ)*c*lam, mul_pos (mul_pos (by norm_num) hc) lam_pos, ?_⟩
  intro x s H η hs hη hPH hHm u hu i
  have hlast : H-1 ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
  have ht := (hη.2.2.1 (H-1) hlast).2.1
  have hα := alpha_ge_lam hs
  have hT : (9/10 : ℝ)*lam*(H-1 : ℕ)*(rho^(H-1))⁻¹ ≤ tailLog η (H-1) := by
    apply le_trans _ ht
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα (by norm_num))
        (Nat.cast_nonneg _)) (inv_pos.mpr (pow_pos rho_pos _)).le
  have hu' := tailPrefixRegion_terminal_lower hη hPH hHm hu i
  have hn : (R x H-i.val)+(H-1) = m x-(i.val+1) := by
    have := i.isLt
    unfold R at *
    omega
  have hp : rho^(m x-(i.val+1)) = rho^(R x H-i.val)*rho^(H-1) := by
    rw [← pow_add, hn]
  calc
    _ = rho^(m x-(i.val+1))*
        ((c*(rho^(R x H-i.val))⁻¹)*
          ((9/10 : ℝ)*lam*(H-1 : ℕ)*(rho^(H-1))⁻¹)) := by
      rw [hp]
      field_simp [rho_pos.ne']
    _ ≤ rho^(m x-(i.val+1))*(g (R x H-i.val)*tailLog η (H-1)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_pos rho_pos _).le
      exact mul_le_mul (hg _) hT (by have := lam_pos; have := rho_pos; positivity) (g_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hu' (pow_pos rho_pos _).le

end TotientAsymptotic

end

end OAI
