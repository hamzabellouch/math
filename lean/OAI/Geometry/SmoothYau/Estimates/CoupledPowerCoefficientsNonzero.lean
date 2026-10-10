import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
lemma coupled_power_coefficients_nonzero {A B w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hw : w ≠ 0) (hAB : A ≠ 0 ∨ B ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    (hF : A^k+(δ:ℂ)*B^k=0) :
    ¬ ((w*A^(k-1)+w*(δ:ℂ)*B^(k-1)).re=0 ∧
      (w*A^(k-1)).im=0 ∧ (w*(δ:ℂ)*B^(k-1)).im=0) := by
  intro h
  have hδ0 : (δ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  have hA : A ≠ 0 := by
    intro ha
    have hB : B^k=0 := by
      simpa only [ha,zero_pow (by omega : k≠0),zero_add,mul_eq_zero, hδ0,false_or] using hF
    exact hAB.elim (fun hh => hh ha) (fun hh => (pow_ne_zero k hh) hB)
  have hC : w*A^(k-1) ≠ 0 := mul_ne_zero hw (pow_ne_zero _ hA)
  have hsum : w*A^(k-1)+w*(δ:ℂ)*B^(k-1)=0 := by
    apply Complex.ext
    · simpa only [Complex.zero_re] using h.1
    · simp only [Complex.add_im,h.2.1,h.2.2,add_zero,Complex.zero_im]
  have hmul : (w*A^(k-1))*A+(w*(δ:ℂ)*B^(k-1))*B=0 := by
    have hAp : A^(k-1)*A=A^k := by rw [←pow_succ, Nat.sub_add_cancel hk]
    have hBp : B^(k-1)*B=B^k := by rw [←pow_succ, Nat.sub_add_cancel hk]
    calc
      _ = w*(A^(k-1)*A+(δ:ℂ)*(B^(k-1)*B)) := by ring
      _ = w*(A^k+(δ:ℂ)*B^k) := by rw [hAp,hBp]
      _ = 0 := by rw [hF,mul_zero]
  have heq : A=B := by
    have hz : (w*A^(k-1))*(A-B)=0 := by linear_combination hmul - B*hsum
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hC)
  rw [←heq] at hF
  have hz : ((1+δ:ℝ):ℂ)*A^k=0 := by push_cast; linear_combination hF
  have hp : ((1+δ:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  exact (mul_ne_zero hp (pow_ne_zero k hA)) hz
end YauCounterexamples
end

end OAI
