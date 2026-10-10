import OAI.NumberTheory.Ostmann.Conclusion.ActualAmplitudeNorm
import OAI.NumberTheory.Ostmann.Conclusion.RegularNormGeneral

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Construction Ostmann.Arithmetic.PrimeCellReplacement

abbrev regularSmallModulus (small : List SmallSlot) : ℕ :=
  ∏ i : Fin small.length, small[i].value

theorem regularSmallModulus_eq (small : List SmallSlot) :
    regularSmallModulus small = (small.map SmallSlot.value).prod := by
  rw [regularSmallModulus, ←List.prod_ofFn]
  exact congrArg List.prod (List.ofFn_getElem_eq_map small SmallSlot.value)

def regularSmallNumerator (outside : List ℕ) (q : ℕ) (small : List SmallSlot)
    (s : ℤ) (i : Fin small.length) : ZMod small[i].value :=
  modFraction small[i].value s (outsideProduct outside*(q*(regularSmallModulus small/small[i].value)))

theorem regular_modFraction_small {r : ℕ} [Fact r.Prime]
    (p q d C : ℕ) (s : ℤ) (hr : r ∣ C) :
    modFraction r s (d*((p*q*C)/r)) =
      modFraction r s (d*(q*(C/r)))*(p : ZMod r)⁻¹ := by
  rw [Nat.mul_div_assoc (p*q) hr]
  simp only [modFraction,Nat.cast_mul,mul_inv_rev]
  ring

theorem supported_regular_giant_coprime (p q : ℕ) (s : ℤ) (small : List SmallSlot)
    (outside : List ℕ) (hs : (State.mk s p q small).Coprime outside) :
    p.Coprime (regularSmallModulus small) := by
  rw [regularSmallModulus_eq]
  apply Nat.coprime_list_prod_right_iff.mpr
  have hh := (List.pairwise_cons.mp (List.pairwise_append.mp hs).1).1
  intro r hr
  exact hh r (List.mem_cons_of_mem q hr)

theorem regularTransform_norm_sq_le (g giant : (p : ℕ) → ZMod p → ℂ)
    (hg : ∀ p x, ‖giant p x‖ ≤ 1) (outside : List ℕ)
    (s : ℤ) (p q : ℕ) (small : List SmallSlot) :
    ‖regularTransform g giant outside (State.mk s p q small)‖^2 ≤
      ∏ i : Fin small.length, ‖g small[i].value
        (modFraction small[i].value s (outsideProduct outside*
          ((State.mk s p q small).product/small[i].value)))‖^2 := by
  unfold regularTransform
  dsimp only
  rw [norm_mul,norm_mul,mul_pow,mul_pow]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hg p (modFraction p s
    (outsideProduct outside*((State.mk s p q small).product/p)))) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hg q (modFraction q s
    (outsideProduct outside*((State.mk s p q small).product/q)))) 2
  norm_num only [one_pow] at h1 h2
  calc
    _ ≤ 1*1*‖(small.map fun r => g r.value (modFraction r.value s
        (outsideProduct outside*((State.mk s p q small).product/r.value)))).prod‖^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by norm_num)) (by positivity)
    _ = _ := by
      rw [one_mul,one_mul,←List.ofFn_getElem_eq_map small (fun r => g r.value (modFraction r.value s
        (outsideProduct outside*((State.mk s p q small).product/r.value)))), List.prod_ofFn, norm_prod, ←Finset.prod_pow]
      rfl

end Ostmann.Conclusion

end

end OAI
