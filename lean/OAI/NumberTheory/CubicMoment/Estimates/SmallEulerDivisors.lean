import OAI.NumberTheory.CubicMoment.Estimates.SmallEulerProduct

namespace OAI

/-! The count and norm of the exact Euler rescalings at a small modulus. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma euler_part_norm_le {v : Eisenstein} (hv : v ≠ 0)
    {T : Finset EisensteinIdealPrime} (hT : T ∈ (idealExponentOf v).support.powerset) :
    idealExponentNorm (primeSetExponent T) ≤ norm v := by
  have hle : primeSetExponent T ≤ idealExponentOf v := by
    apply (primeSetExponent_le_iff T (idealExponentOf v)).mpr
    intro p hp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Finset.mem_powerset.mp hT) hp))
  have hnorm := norm_le_of_dvd (idealExponentGenerator_ne_zero (idealExponentOf v))
    (idealExponentGenerator_dvd_of_le hle)
  have hn : idealExponentNorm (primeSetExponent T) ≤ idealExponentNorm (idealExponentOf v) := by
    simpa only [idealExponentNorm,normNat_cast] using hnorm
  rwa [idealExponentOf_norm hv] at hn

 theorem euler_parts_card_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Eisenstein, v ≠ 0 →
      (((idealExponentOf v).support.powerset).card:ℝ) ≤ C*norm v^ε := by
  obtain ⟨C,hC,hbound⟩ := ideal_divisor_product_small_power hε
  refine ⟨C,hC,?_⟩
  intro v hv
  have hpoint : ∀ p ∈ (idealExponentOf v).support,
      (2:ℝ) ≤ (idealExponentOf v p:ℝ)+1 := by
    intro p hp
    have hn : (1:ℝ) ≤ idealExponentOf v p := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp))
    linarith
  calc
    _ = ∏ _p ∈ (idealExponentOf v).support, (2:ℝ) := by
      simp only [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,Finset.prod_const]
    _ ≤ ∏ p ∈ (idealExponentOf v).support, ((idealExponentOf v p:ℝ)+1) :=
      Finset.prod_le_prod₀ (fun _ _ => by norm_num) hpoint
    _ ≤ C*idealExponentNorm (idealExponentOf v)^ε := hbound _
    _ = C*norm v^ε := by rw [idealExponentOf_norm hv]

end CubicFirstMoment

end

end OAI
