import Mathlib
import OAI.Combinatorics.UniformKServer.Disintegration

namespace OAI

noncomputable section

/-! Expectations only charge positive support. -/
namespace UniformKServer.FiniteProbability
open Finset
open scoped Classical
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem Law.expect_mono_support (P : Law Ω) (f g : Ω→ℝ)
    (h : ∀ x,0<P.weight x → f x≤g x) : P.expect f≤P.expect g := by
  apply sum_le_sum
  intro x _
  by_cases hx : 0<P.weight x
  · exact mul_le_mul_of_nonneg_left (h x hx) hx.le
  · have hz := le_antisymm (not_lt.mp hx) (P.nonneg x)
    rw [hz,zero_mul,zero_mul]

theorem Law.map_comp (P : Law Ω) (f : Ω→Γ) {Δ : Type*} [Fintype Δ] (g : Γ→Δ) :
    (P.map f).map g=P.map (g ∘ f) := by
  apply Law.ext_expect
  intro h
  simp only [Law.expect_map,Function.comp_assoc]

theorem Law.map_id (P : Law Ω) : P.map id=P := by
  apply Law.ext_expect
  intro h
  simp only [Law.expect_map,Function.comp_id]

theorem Law.nonempty (P : Law Ω) : Nonempty Ω := by
  by_contra hn
  have : IsEmpty Ω := ⟨fun x=>hn ⟨x⟩⟩
  have := P.total
  simp at this

theorem Law.expect_univ (P : Law Ω) (f : Γ→Ω→ℝ) :
    P.expect (fun ω=>∑ i,f i ω)=∑ i,P.expect (f i) := by
  simp only [Law.expect,mul_sum]
  rw [sum_comm]

end UniformKServer.FiniteProbability

end

end OAI
