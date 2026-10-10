import OAI.NumberTheory.Ostmann.Characters.FactorialContradiction
import OAI.NumberTheory.Ostmann.Characters.PermutationComparison

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.Characters
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem parity_permutation_comparison (n m : ℕ)
    (f : ParityReassignments n m → E) (w : E) (η : ℂ)
    {D e : ℝ} (he : 0 ≤ e) (hmean : ∀ i, inner ℂ w (f i) = η)
    (hdiag : ∀ i, ‖f i‖^2 ≤ D)
    (hoff : ∀ i j, i ≠ j → ‖inner ℂ (f i) (f j)‖ ≤ e) :
    ‖η‖^2 ≤ ‖w‖^2 * (D / (factorialCount n m : ℝ) + e) := by
  have h := permutation_comparison f w η he hmean hdiag hoff
  rw [← factorialCount_eq_card] at h
  have hJ : (0 : ℝ) < factorialCount n m := by exact_mod_cast factorialCount_pos n m
  apply le_of_mul_le_mul_left (a := (factorialCount n m : ℝ)^2) _ (sq_pos_of_pos hJ)
  convert h using 1
  field_simp

theorem parity_family_impossible (n m : ℕ) (B v C K c α L : ℝ)
    (hK : 0 ≤ K)
    (hcomparison :
      2 * Real.exp (v * factorialMass n m) *
        (Real.exp (C * factorialMass n m) / (factorialCount n m : ℝ) +
          K * Real.exp (-c * Real.exp (α * L))) <
      Real.exp (-2*B * factorialMass n m))
    (f : ParityReassignments n m → E) (w : E) (η : ℂ)
    (hmean : ∀ i, inner ℂ w (f i) = η)
    (hamp : Real.exp (-B * factorialMass n m) ≤ ‖η‖)
    (hmass : ‖w‖^2 ≤ 2 * Real.exp (v * factorialMass n m))
    (hdiag : ∀ i, ‖f i‖^2 ≤ Real.exp (C * factorialMass n m))
    (hoff : ∀ i j, i ≠ j →
      ‖inner ℂ (f i) (f j)‖ ≤ K * Real.exp (-c * Real.exp (α * L))) : False := by
  have he : 0 ≤ K * Real.exp (-c * Real.exp (α * L)) :=
    mul_nonneg hK (Real.exp_nonneg _)
  have h := parity_permutation_comparison n m f w η he hmean hdiag hoff
  have hJ : (0 : ℝ) ≤ factorialCount n m := Nat.cast_nonneg _
  have hbracket : 0 ≤ Real.exp (C * factorialMass n m) / (factorialCount n m : ℝ) +
      K * Real.exp (-c * Real.exp (α * L)) :=
    add_nonneg (div_nonneg (Real.exp_nonneg _) hJ) he
  have hupper := h.trans (mul_le_mul_of_nonneg_right hmass hbracket)
  have hlower : Real.exp (-2*B * factorialMass n m) ≤ ‖η‖^2 := by
    calc
      _ = (Real.exp (-B * factorialMass n m))^2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hamp 2
  exact (not_lt_of_ge hlower) (hupper.trans_lt hcomparison)

theorem exists_depth_no_parity_families (B BD C ε : ℝ)
    (hε : 60*ε < Real.log 2) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ ∀ (z c α K : ℝ), 0 < z → 0 < c → 0 < α → 0 ≤ K →
      ∀ᶠ L : ℝ in atTop,
        ∀ (f : ParityReassignments n (factorialBulk z L) → E) (w : E) (η : ℂ),
          (∀ i, inner ℂ w (f i) = η) →
          Real.exp (-B * factorialMass n (factorialBulk z L)) ≤ ‖η‖ →
          ‖w‖^2 ≤ 2 * Real.exp ((BD+60*ε*(n+1)) *
            factorialMass n (factorialBulk z L)) →
          (∀ i, ‖f i‖^2 ≤ Real.exp (C * factorialMass n (factorialBulk z L))) →
          (∀ i j, i ≠ j → ‖inner ℂ (f i) (f j)‖ ≤
            K * Real.exp (-c * Real.exp (α * L))) → False := by
  obtain ⟨n, hn, h⟩ := exists_depth_factorial_comparison B BD C ε hε n₀
  refine ⟨n, hn, ?_⟩
  intro z c α K hz hc hα hK
  filter_upwards [h z c α K hz hc hα] with L hL
  exact parity_family_impossible n (factorialBulk z L) B (BD+60*ε*(n+1)) C K c α L hK hL

end
end Ostmann.Characters

end

end OAI
