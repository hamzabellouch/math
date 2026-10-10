import OAI.NumberTheory.Ostmann.QuadraticCenter.FourthMomentFamily

namespace OAI

/-!
# Cauchy--Schwarz for the two-bad quartet twists

The two character changes are permutations. After excluding principal
twists, the two squared energies are exactly the fourth-moment sums.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance twistCauchyFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance twistCauchyDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

private theorem sum_nonprincipal_twist {p : ℕ} [Fact p.Prime]
    (ν : MulChar (ZMod p) ℂ) (f : MulChar (ZMod p) ℂ → ℝ) :
    (∑ ψ : MulChar (ZMod p) ℂ, if ν * ψ⁻¹ ≠ 1 then f (ν * ψ⁻¹) else 0) =
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1, f α := by
  classical
  let e := (Equiv.inv (MulChar (ZMod p) ℂ)).trans (Equiv.mulLeft ν)
  calc
    _ = ∑ α : MulChar (ZMod p) ℂ, if α ≠ 1 then f α else 0 :=
      e.bijective.sum_comp (fun α => if α ≠ 1 then f α else 0)
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext α
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true]

/-- The nonprincipal part of the two-bad sum is controlled by two fourth moments. -/
theorem two_bad_twist_cauchy {p : ℕ} [Fact p.Prime]
    (F G : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (ν : MulChar (ZMod p) ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
        ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0) ^ 2 ≤
      (∑ χ : MulChar (ZMod p) ℂ,
        ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
          ∑ a : ZMod p, ‖F χ α a‖ ^ 4) *
      (∑ ψ : MulChar (ZMod p) ℂ,
        ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
          ∑ a : ZMod p, ‖G ψ β a‖ ^ 4) := by
  classical
  let u : MulChar (ZMod p) ℂ × (MulChar (ZMod p) ℂ × ZMod p) → ℝ :=
    fun t => if ν * t.2.1⁻¹ ≠ 1 then ‖F t.1 (ν * t.2.1⁻¹) t.2.2‖ ^ 2 else 0
  let v : MulChar (ZMod p) ℂ × (MulChar (ZMod p) ℂ × ZMod p) → ℝ :=
    fun t => if ν⁻¹ * t.1⁻¹ ≠ 1 then ‖G t.2.1 (ν⁻¹ * t.1⁻¹) (-t.2.2)‖ ^ 2 else 0
  have hprod : (∑ t, u t * v t) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
          ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0 := by
    simp only [Fintype.sum_prod_type, u, v]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro ψ _
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  have hu : (∑ t, u t ^ 2) =
      ∑ χ : MulChar (ZMod p) ℂ,
        ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
          ∑ a : ZMod p, ‖F χ α a‖ ^ 4 := by
    simp only [Fintype.sum_prod_type, u, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      ← pow_mul, (show (2 : ℕ) * 2 = 4 by decide)]
    apply Finset.sum_congr rfl
    intro χ _
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    exact sum_nonprincipal_twist ν (fun α => ∑ a : ZMod p, ‖F χ α a‖ ^ 4)
  have hv : (∑ t, v t ^ 2) =
      ∑ ψ : MulChar (ZMod p) ℂ,
        ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
          ∑ a : ZMod p, ‖G ψ β a‖ ^ 4 := by
    simp only [Fintype.sum_prod_type, v, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      ← pow_mul, (show (2 : ℕ) * 2 = 4 by decide)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ψ _
    have hneg (β : MulChar (ZMod p) ℂ) : (∑ a : ZMod p, ‖G ψ β (-a)‖ ^ 4) =
        ∑ a : ZMod p, ‖G ψ β a‖ ^ 4 :=
      (Equiv.neg (ZMod p)).bijective.sum_comp (fun a => ‖G ψ β a‖ ^ 4)
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, hneg]
    exact sum_nonprincipal_twist ν⁻¹ (fun β => ∑ a : ZMod p, ‖G ψ β a‖ ^ 4)
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  rwa [hprod, hu, hv] at h

end Ostmann

end OAI
