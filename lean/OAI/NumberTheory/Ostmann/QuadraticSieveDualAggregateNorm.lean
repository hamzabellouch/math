import OAI.NumberTheory.Ostmann.QuadraticSieveDualWindows
import OAI.NumberTheory.Ostmann.QuadraticSieveExponentIterationInitial
import OAI.NumberTheory.Ostmann.QuadraticSieveNormReciprocity
import OAI.NumberTheory.Ostmann.QuadraticSieveNormSupport

namespace OAI

namespace Ostmann.QuadraticSieve

@[simp] theorem quadraticNorm_empty_columns (V : Finset ℕ) : quadraticNorm V ∅ = 0 := by
  apply le_antisymm
  · simpa only [Finset.card_empty, Nat.cast_zero, mul_zero] using quadraticNorm_le_card_mul V ∅
  · exact quadraticNorm_nonneg V ∅

@[simp] theorem oddSquarefreeUpTo_zero : oddSquarefreeUpTo 0 = ∅ := by
  simp [oddSquarefreeUpTo]

theorem exponentBound_smaller_norm {ξ : ℝ}
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B N j : ℕ) (V : Finset ℕ), 0 < B → 0 < N → 0 < j →
      V ⊆ oddSquarefreeUpTo B →
      quadraticNorm V (oddSquarefreeUpTo (N/j)) ≤
        C * ((B : ℝ)*N)^δ * ((B : ℝ)^ξ + (N : ℝ)/j) := by
  obtain ⟨C,hC,hbound⟩ := hξ δ hδ
  refine ⟨2*C,by positivity,?_⟩
  intro B N j V hB hN hj hV
  have hq : ((N/j : ℕ) : ℝ) ≤ (N : ℝ)/j := Nat.cast_div_le
  have hqN : (N/j : ℕ) ≤ N := Nat.div_le_self N j
  have hprod : (((N/j : ℕ) : ℝ)*(B : ℝ))^δ ≤ ((B : ℝ)*N)^δ := by
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    have h := mul_le_mul_of_nonneg_right (show ((N/j : ℕ) : ℝ) ≤ N by exact_mod_cast hqN)
      (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
    simpa only [mul_comm] using h
  by_cases hz : N/j = 0
  · rw [hz, oddSquarefreeUpTo_zero, quadraticNorm_empty_columns]
    positivity
  · have hp : 0 < N/j := Nat.pos_of_ne_zero hz
    calc
      quadraticNorm V (oddSquarefreeUpTo (N/j)) ≤
          quadraticNorm (oddSquarefreeUpTo B) (oddSquarefreeUpTo (N/j)) :=
        quadraticNorm_mono_rows hV _
      _ ≤ 2*quadraticNorm (oddSquarefreeUpTo (N/j)) (oddSquarefreeUpTo B) :=
        quadraticNorm_le_two_swap _ _
          (fun v hv => (mem_oddSquarefreeUpTo.mp hv).2.2.1)
          (fun n hn => (mem_oddSquarefreeUpTo.mp hn).2.2.1)
      _ ≤ 2*(C*((((N/j : ℕ) : ℝ))*B)^δ*(((N/j : ℕ) : ℝ)+(B : ℝ)^ξ)) :=
        mul_le_mul_of_nonneg_left (hbound (N/j) B hp hB) (by norm_num)
      _ ≤ 2*(C*((B : ℝ)*N)^δ*((N : ℝ)/j+(B : ℝ)^ξ)) := by
        gcongr
      _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
