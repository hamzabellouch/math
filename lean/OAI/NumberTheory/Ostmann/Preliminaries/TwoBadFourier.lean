import OAI.NumberTheory.Ostmann.Characters.QuartetFourier

namespace OAI

/-!
# Joining the four cases of the two-bad quartet sum

The nonprincipal part uses the fourth moment. The two cases with exactly
one principal twist use its total energy and the other twist's maximum.
The last case uses the principal maximum and a single energy bound.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance twoBadFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance twoBadDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

/-- A common fourth-moment bound controls all nonprincipal terms. -/
theorem two_bad_nonprincipal_le {p : ℕ} [Fact p.Prime]
    (F G : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (ν : MulChar (ZMod p) ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hF : (∑ χ : MulChar (ZMod p) ℂ,
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖F χ α a‖ ^ 4) ≤ T)
    (hG : (∑ ψ : MulChar (ZMod p) ℂ,
      ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖G ψ β a‖ ^ 4) ≤ T) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
        ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0) ≤ T := by
  have hFn : 0 ≤ ∑ χ : MulChar (ZMod p) ℂ,
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖F χ α a‖ ^ 4 := by positivity
  have hGn : 0 ≤ ∑ ψ : MulChar (ZMod p) ℂ,
      ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖G ψ β a‖ ^ 4 := by positivity
  have h := (two_bad_twist_cauchy F G ν).trans (mul_le_mul hF hG hGn hT)
  nlinarith

/-- The complete two-bad sum, including both principal-character exceptions. -/
theorem two_bad_fourier_sum_le {p : ℕ} [Fact p.Prime]
    (F G : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (ν : MulChar (ZMod p) ℂ) (T K M R S : ℝ)
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hF4 : (∑ χ : MulChar (ZMod p) ℂ,
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖F χ α a‖ ^ 4) ≤ T)
    (hG4 : (∑ ψ : MulChar (ZMod p) ℂ,
      ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖G ψ β a‖ ^ 4) ≤ T)
    (hFn : ∀ χ α, α ≠ 1 → ∀ a, ‖F χ α a‖ ^ 2 ≤ K)
    (hGn : ∀ ψ β, β ≠ 1 → ∀ a, ‖G ψ β a‖ ^ 2 ≤ K)
    (hFp : ∀ χ a, ‖F χ 1 a‖ ^ 2 ≤ M)
    (hFsum : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖F χ 1 a‖ ^ 2) ≤ S)
    (hGsum : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖G ψ 1 a‖ ^ 2) ≤ S)
    (hGenergy : ∀ ψ, (∑ a : ZMod p, ‖G ψ 1 a‖ ^ 2) ≤ R) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2) ≤
      T + 2 * K * S + M * R := by
  classical
  let n := ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
    if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
      ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0
  have hn : n ≤ T := two_bad_nonprincipal_le F G ν T hT hF4 hG4
  have hneg (ψ : MulChar (ZMod p) ℂ) :
      (∑ a : ZMod p, ‖G ψ 1 (-a)‖ ^ 2) = ∑ a : ZMod p, ‖G ψ 1 a‖ ^ 2 :=
    (Equiv.neg (ZMod p)).bijective.sum_comp (fun a => ‖G ψ 1 a‖ ^ 2)
  have hp (χ ψ : MulChar (ZMod p) ℂ) (a : ZMod p) :
      ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 ≤
        (if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
          ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0) +
        (if ψ = ν then K * ‖F χ 1 a‖ ^ 2 else 0) +
        (if χ = ν⁻¹ then K * ‖G ψ 1 (-a)‖ ^ 2 else 0) +
        (if χ = ν⁻¹ ∧ ψ = ν then M * ‖G ψ 1 (-a)‖ ^ 2 else 0) := by
    by_cases hα : ν * ψ⁻¹ = 1 <;> by_cases hβ : ν⁻¹ * χ⁻¹ = 1
    · have hψ : ψ = ν := (mul_inv_eq_one.mp hα).symm
      have hχ : χ = ν⁻¹ := (mul_inv_eq_one.mp hβ).symm
      simp [hχ, hψ]
      have h := mul_le_mul_of_nonneg_right (hFp ν⁻¹ a) (sq_nonneg ‖G ν 1 (-a)‖)
      have h₁ := mul_nonneg hK (sq_nonneg ‖F ν⁻¹ 1 a‖)
      have h₂ := mul_nonneg hK (sq_nonneg ‖G ν 1 (-a)‖)
      linarith
    · have hψ : ψ = ν := (mul_inv_eq_one.mp hα).symm
      have hχ : χ ≠ ν⁻¹ := by intro h; apply hβ; simp [h]
      simpa [hψ, hχ, hβ, mul_comm] using
        mul_le_mul_of_nonneg_right (hGn ν _ hβ (-a)) (sq_nonneg ‖F χ 1 a‖)
    · have hψ : ψ ≠ ν := by intro h; apply hα; simp [h]
      have hχ : χ = ν⁻¹ := (mul_inv_eq_one.mp hβ).symm
      simpa [hχ, hψ, hα] using
        mul_le_mul_of_nonneg_right (hFn ν⁻¹ _ hα a) (sq_nonneg ‖G ψ 1 (-a)‖)
    · have hψ : ψ ≠ ν := by intro h; apply hα; simp [h]
      have hχ : χ ≠ ν⁻¹ := by intro h; apply hβ; simp [h]
      simp [hα, hβ, hψ, hχ]
  calc
    _ ≤ n + K * (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖F χ 1 a‖ ^ 2) +
        K * (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖G ψ 1 a‖ ^ 2) +
        M * (∑ a : ZMod p, ‖G ν 1 a‖ ^ 2) := by
      calc
        _ ≤ ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
            ((if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
              ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0) +
            (if ψ = ν then K * ‖F χ 1 a‖ ^ 2 else 0) +
            (if χ = ν⁻¹ then K * ‖G ψ 1 (-a)‖ ^ 2 else 0) +
            (if χ = ν⁻¹ ∧ ψ = ν then M * ‖G ψ 1 (-a)‖ ^ 2 else 0)) :=
          Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun ψ _ =>
            Finset.sum_le_sum fun a _ => hp χ ψ a
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
            Finset.sum_const_zero, n]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          simp only [← Finset.mul_sum, hneg]
          simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ ≤ T + K * S + K * S + M * R := by
      exact add_le_add (add_le_add (add_le_add hn
        (mul_le_mul_of_nonneg_left hFsum hK))
        (mul_le_mul_of_nonneg_left hGsum hK))
        (mul_le_mul_of_nonneg_left (hGenergy ν) hM)
    _ = _ := by ring

end Ostmann

end OAI
