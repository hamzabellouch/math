import Mathlib
import OAI.Combinatorics.UniformKServer.LawKernel

namespace OAI

noncomputable section

/-! Exact finite disintegration, including all null fibers. -/
namespace UniformKServer.FiniteProbability
open Finset
open scoped Classical
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem Law.ext {P Q : Law Ω} (h : P.weight=Q.weight) : P=Q := by
  cases P; cases Q; cases h; rfl

theorem Law.ext_expect {P Q : Law Ω} (h : ∀ f : Ω→ℝ,P.expect f=Q.expect f) : P=Q := by
  apply Law.ext
  funext x
  have := h (fun y=>if y=x then 1 else 0)
  simpa [Law.expect] using this

theorem Law.weighted_conditional (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (y : Γ) (g : Ω→ℝ) :
    (P.map f).weight y*(P.conditional f fallback y).expect g=
      ∑ x,if f x=y then P.weight x*g x else 0 := by
  by_cases hy : 0<(P.map f).weight y
  · simp only [Law.conditional,dite_eq_left hy,Law.expect,mul_sum]
    apply sum_congr rfl
    intro x _
    split_ifs
    · field_simp
    · simp
  · have hz := le_antisymm (not_lt.mp hy) ((P.map f).nonneg y)
    rw [hz,zero_mul]
    symm
    apply sum_eq_zero
    intro x _
    split_ifs with he
    · have hh : P.weight x≤(P.map f).weight y := by
        change _≤∑ z,if f z=y then P.weight z else 0
        have := single_le_sum (s:=(univ : Finset Ω))
          (f:=fun z=>if f z=y then P.weight z else 0)
          (fun z _=>by split; exact P.nonneg z; exact le_rfl) (mem_univ x)
        simpa only [ite_eq_left he] using this
      have hx := le_antisymm (hh.trans hz.le) (P.nonneg x)
      rw [hx,zero_mul]
    · rfl

theorem Law.disintegrate (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (g : Γ→Ω→ℝ) :
    (P.map f).expect (fun y=>(P.conditional f fallback y).expect (g y))=
      P.expect (fun x=>g (f x) x) := by
  unfold Law.expect
  have hr (y : Γ) := P.weighted_conditional f fallback y (g y)
  change ∑ y,(P.map f).weight y*(P.conditional f fallback y).expect (g y)=_
  simp_rw [hr]
  rw [sum_comm]
  simp

theorem Law.conditional_positive (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (y : Γ)
    (hy : 0<(P.map f).weight y) (x : Ω) (hx : 0<(P.conditional f fallback y).weight x) :
    f x=y ∧ 0<P.weight x := by
  simp only [Law.conditional,dite_eq_left hy] at hx
  split_ifs at hx with he
  · exact ⟨he,(div_pos_iff.mp hx).resolve_right (fun h=>not_lt_of_ge hy.le h.2) |>.1⟩
  · simp at hx

theorem Law.weight_le_map (P : Law Ω) (f : Ω→Γ) (x : Ω) :
    P.weight x ≤ (P.map f).weight (f x) := by
  have h := single_le_sum (s:=(univ : Finset Ω))
    (f:=fun y=>if f y=f x then P.weight y else 0)
    (fun y _=>by split; exact P.nonneg y; exact le_rfl) (mem_univ x)
  simpa [Law.map] using h

end UniformKServer.FiniteProbability

end

end OAI
