import OAI.NumberTheory.Ostmann.Characters.GcdFrequencyTree

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.ReducedFrequencyTree
open Arithmetic.FrequencyMultiplicity

def factor (ε C:ℝ) (_p:List Bool) (s v w:ℤ) : ℝ :=
  C*(reducedModulus v w s:ℝ)^(ε-1)

theorem root_sum_le (ε:ℝ) (hε:0≤ε) (C:ℝ) (hC:0≤C)
    (v w:ℤ) (hv:v≠0) (S:Finset ℤ) (V:ℕ)
    (hS:∀s∈S,s≠0 ∧ s.natAbs≤V) :
    (∑s∈S,C*(reducedModulus v w s:ℝ)^(ε-1)) ≤
      C*(V:ℝ)^ε*(2*((v.natAbs.gcd w.natAbs).divisors.card:ℝ)*(1+Real.log V)) := by
  have hb (s:ℤ) (hs:s∈S) : (reducedModulus v w s:ℝ)^(ε-1)≤
      (V:ℝ)^ε*(reducedModulus v w s:ℝ)⁻¹ := by
    have ha := Finset.mem_Icc.mp (reducedModulus_mem_Icc v w s (hS s hs).1 V (hS s hs).2)
    have haR : (0:ℝ)<reducedModulus v w s := by exact_mod_cast (Nat.zero_lt_of_lt ha.1)
    rw [Real.rpow_sub_one haR.ne',div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow haR.le (by exact_mod_cast ha.2) hε) (by positivity)
  calc
    _ ≤ ∑s∈S,(C*(V:ℝ)^ε)*(reducedModulus v w s:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro s hs
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb s hs) hC
    _ = (C*(V:ℝ)^ε)*(∑s∈S,(reducedModulus v w s:ℝ)⁻¹) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_reduced_sum_le_log v w hv S V hS)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem total_le (ε:ℝ) (hε:0<ε) :
    ∃ D:ℝ, 0<D ∧ ∀ C:ℝ, 0≤C → ∀ S:List Bool→Finset ℤ, ∀ V:List Bool→ℕ,
      (∀p,1≤V p) → (∀p s,s∈S p→s≠0 ∧ s.natAbs≤V p) → ∀ k p,
      FrequencyTreeSum.total S (factor ε C) k p ≤
        FrequencyTreeSum.budget S
          (fun p=>C*(V p:ℝ)^ε*(2*D*(V (false::p):ℝ)^ε*(1+Real.log (V p)))) k p := by
  obtain ⟨D,hD,hτ⟩ := Arithmetic.divisors_card_le_rpow ε hε
  refine ⟨D,hD,?_⟩
  intro C hC S V hV hS k p
  apply FrequencyTreeSum.total_le_budget
  · intro p s v w
    exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p
    have hl : 0≤Real.log (V p) := Real.log_nonneg (by exact_mod_cast hV p)
    positivity
  · intro p v hv w hw
    have hv0 : v≠0 := (hS _ _ hv).1
    have hg : 0<v.natAbs.gcd w.natAbs := Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hv0)
    have hgv : v.natAbs.gcd w.natAbs≤V (false::p) :=
      (Nat.gcd_le_left _ (Int.natAbs_pos.mpr hv0)).trans (hS _ _ hv).2
    have ht : ((v.natAbs.gcd w.natAbs).divisors.card:ℝ)≤D*(V (false::p):ℝ)^ε :=
      (hτ _ hg).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hgv) hε.le) hD.le)
    have hl : 0≤1+Real.log (V p) :=
      add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hV p))
    exact (root_sum_le ε hε.le C hC v w hv0 (S p) (V p) (hS p)).trans
      (mul_le_mul_of_nonneg_left
        (by nlinarith [mul_le_mul_of_nonneg_right ht hl])
        (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

end Ostmann.Characters.ReducedFrequencyTree

end

end OAI
