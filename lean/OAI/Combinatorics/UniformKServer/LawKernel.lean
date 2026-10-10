import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteProbability

namespace OAI

                                
section

/-! Exact push-forward and finite conditional kernels, including null rows. -/
noncomputable section
namespace UniformKServer.FiniteProbability
open Finset
open scoped Classical
variable {Ω Γ Δ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ]

def Law.map (P : Law Ω) (f : Ω→Γ) : Law Γ where
  weight y := ∑ x,if f x=y then P.weight x else 0
  nonneg y := sum_nonneg (fun x _=>by split; exact P.nonneg x; exact le_rfl)
  total := by rw [sum_comm]; simp [P.total]

theorem Law.expect_map (P : Law Ω) (f : Ω→Γ) (g : Γ→ℝ) :
    (P.map f).expect g=P.expect (g ∘ f) := by
  simp only [Law.expect,Law.map,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

def Law.pure (x : Ω) : Law Ω where
  weight y := if y=x then 1 else 0
  nonneg y := by split <;> norm_num
  total := by simp

theorem Law.expect_pure (x : Ω) (f : Ω→ℝ) : (Law.pure x).expect f=f x := by simp [Law.expect,Law.pure]

def Law.bind (P : Law Ω) (K : Ω→Law Γ) : Law Γ where
  weight y := ∑ x,P.weight x*(K x).weight y
  nonneg y := sum_nonneg (fun x _=>mul_nonneg (P.nonneg x) ((K x).nonneg y))
  total := by rw [sum_comm]; simp only [←mul_sum,(K _).total,mul_one,P.total]

theorem Law.expect_bind (P : Law Ω) (K : Ω→Law Γ) (f : Γ→ℝ) :
    (P.bind K).expect f=P.expect (fun x=>(K x).expect f) := by
  simp only [Law.expect,Law.bind,sum_mul,mul_sum,mul_assoc]
  rw [sum_comm]

def Law.conditional (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (y : Γ) : Law Ω :=
  if h : 0<(P.map f).weight y then {
    weight x := (if f x=y then P.weight x else 0)/(P.map f).weight y
    nonneg x := div_nonneg (by split; exact P.nonneg x; exact le_rfl) h.le
    total := by rw [←sum_div]; exact div_self (ne_of_gt h) }
  else fallback

theorem Law.conditional_identity (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (g : Ω→ℝ) :
    (P.map f).expect (fun y=>(P.conditional f fallback y).expect g)=P.expect g := by
  have hn (x : Ω) (y : Γ) (h : (P.map f).weight y=0) (he : f x=y) : P.weight x=0 := by
    have hh : P.weight x≤(P.map f).weight y := by
      change _≤∑ z,if f z=y then P.weight z else 0
      have := single_le_sum (s:=(univ : Finset Ω))
        (f:=fun z=>if f z=y then P.weight z else 0)
        (fun z _=>by split; exact P.nonneg z; exact le_rfl) (mem_univ x)
      simpa only [ite_eq_left he] using this
    exact le_antisymm (hh.trans h.le) (P.nonneg x)
  unfold Law.expect
  have row (y : Γ) : (P.map f).weight y*(∑ x,(P.conditional f fallback y).weight x*g x)=
      ∑ x,if f x=y then P.weight x*g x else 0 := by
    by_cases hy : 0<(P.map f).weight y
    · simp only [Law.conditional,dite_eq_left hy,mul_sum]
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
      · rw [hn x y hz he,zero_mul]
      · rfl
  rw [show (∑ y,(P.map f).weight y*(∑ x,(P.conditional f fallback y).weight x*g x))=
    ∑ y,∑ x,if f x=y then P.weight x*g x else 0 from sum_congr rfl (fun y _=>row y),sum_comm]
  simp

end UniformKServer.FiniteProbability

end


end

end OAI
