import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowth
import OAI.NumberTheory.Ostmann.Characters.FrequencyHarmonic
import OAI.NumberTheory.Ostmann.Characters.FrequencyTreeSum

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.GcdFrequencyTree

def factor (_p:List Bool) (s v w:ℤ) : ℝ :=
  (((v.natAbs.gcd w.natAbs).gcd s.natAbs:ℕ):ℝ)/(s.natAbs:ℝ)

theorem total_le (ε:ℝ) (hε:0<ε) :
    ∃ C:ℝ, 0<C ∧ ∀ S:List Bool→Finset ℤ, ∀ V:List Bool→ℕ,
      (∀p,1≤V p) → (∀p s,s∈S p→s≠0 ∧ s.natAbs≤V p) → ∀ k p,
      FrequencyTreeSum.total S factor k p ≤
        FrequencyTreeSum.budget S
          (fun p=>2*C*(V (false::p):ℝ)^ε*(1+Real.log (V p))) k p := by
  obtain ⟨C,hC,hτ⟩ := Arithmetic.divisors_card_le_rpow ε hε
  refine ⟨C,hC,?_⟩
  intro S V hV hS k p
  apply FrequencyTreeSum.total_le_budget
  · intro p s v w
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro p
    have hl : 0≤Real.log (V p) := Real.log_nonneg (by exact_mod_cast hV p)
    positivity
  · intro p v hv w hw
    have hv0 : v≠0 := (hS _ _ hv).1
    have hg : 0<v.natAbs.gcd w.natAbs :=
      Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hv0)
    have hgv : v.natAbs.gcd w.natAbs≤V (false::p) :=
      (Nat.gcd_le_left _ (Int.natAbs_pos.mpr hv0)).trans (hS _ _ hv).2
    have hpow : ((v.natAbs.gcd w.natAbs:ℕ):ℝ)^ε≤(V (false::p):ℝ)^ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hgv) hε.le
    have hτ' : ((v.natAbs.gcd w.natAbs).divisors.card:ℝ)≤C*(V (false::p):ℝ)^ε :=
      (hτ _ hg).trans (mul_le_mul_of_nonneg_left hpow hC.le)
    have hl : 0≤1+Real.log (V p) :=
      add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hV p))
    calc
      _ ≤ 2*((v.natAbs.gcd w.natAbs).divisors.card:ℝ)*(1+Real.log (V p)) :=
        gcd_frequency_sum_le_log v w hv0 (S p) (V p) (hS p)
      _ ≤ 2*(C*(V (false::p):ℝ)^ε)*(1+Real.log (V p)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ' (by norm_num)) hl
      _ = _ := by ring

end Ostmann.Characters.GcdFrequencyTree

end

end OAI
