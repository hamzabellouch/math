import OAI.NumberTheory.TotientAsymptotic.UnbandedPrefixLower
import OAI.NumberTheory.TotientAsymptotic.EnlargementTail

namespace OAI

/-! A uniform linear envelope for Ford's reverse-indexed enlarged prefixes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem reverse_enlarged_linear_lower : ∃ c : ℝ, 0 < c ∧
    ∀ m N : ℕ, N ≤ m → ∀ B : ℝ, ∀ u : Fin N → ℝ,
      u ∈ enlargedSimplex N B (1+simplexBoxError 0 m)
        (fun i => 1+simplexBoxError 0 (m-(i.val+1))) →
      (∀ i, i.val+1=N → (1/100:ℝ) ≤ u i) → ∀ i, c*(N-i.val:ℕ) ≤ u i := by
  obtain ⟨d,hd,hlower⟩ := enlarged_prefix_linear_lower
  let E := Real.exp (∑' n : ℕ, (n:ℝ)*simplexBoxError 0 n)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨d/(100*E),div_pos hd (mul_pos (by norm_num) hE),?_⟩
  intro m N hNm B u hu hlast
  cases N with
  | zero => intro i; exact Fin.elim0 i
  | succ N =>
    let β : ℕ → ℝ := fun r => 1+simplexBoxError 0 (m-r)
    let κ : Fin (N+1) → ℝ := enlargementScale β
    have hβ (r) : 1 ≤ β r := by
      dsimp [β]
      linarith [simplexBoxError_nonneg (by norm_num : (0:ℝ) ≤ 0) (m-r)]
    have hκ (i) : 1 ≤ κ i ∧ κ i ≤ E := by
      refine ⟨(hβ 0).trans (enlargementScale_top hβ i),?_⟩
      have hh := reverse_enlargement_coordinate (m:=m) (H:=0) (Nat.zero_le m)
        (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
        (summable_simplexBoxError_weighted 0) i (by have := i.isLt; omega)
      simpa only [Nat.zero_add] using hh
    have hh := hlower hE (zero_lt_one.trans_le (hβ 0))
      (fun i => zero_lt_one.trans_le (hβ (i.val+1))) hκ
      (enlargementScale_top hβ) (enlargementScale_step hβ)
      (enlargedSimplex_mul_const hu (by norm_num : (0:ℝ) ≤ 100))
      (by have ht := hlast (Fin.last N) (by simp); linarith)
    intro i
    have hi := hh i
    calc
      _ = (d/E*((N+1-i.val:ℕ):ℝ))/100 := by ring
      _ ≤ u i := (div_le_iff₀ (by norm_num : (0:ℝ)<100)).mpr (by linarith only [hi])

end TotientAsymptotic

end

end OAI
