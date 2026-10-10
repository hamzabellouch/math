import Mathlib
import OAI.Combinatorics.UniformKServer.KeySizeTracker
import OAI.Combinatorics.UniformKServer.AnchorScalar

namespace OAI

                                      
section

/-! Finite heavy-slot potentials and the non-event-conditioned parameter
substeps. This is scalar accounting, not an assumption of the travel budget. -/
noncomputable section
namespace UniformKServer.AnchorPotential
open Finset
open scoped Classical
variable {X H T Ω : Type*} [Fintype H] [MetricSpace X] [Fintype Ω]

def integral (r : ℝ) (μ : X→ℝ) (C : Finset X) (a : X) : ℝ :=
  ∑ p∈C,μ p*AnchorRamp.value r a p

theorem integral_nonneg (r : ℝ) (μ : X→ℝ) (hμ : ∀ p,0 ≤ μ p) (C : Finset X) (a : X) :
    0 ≤ integral r μ C a := sum_nonneg (fun p _=>mul_nonneg (hμ p) (AnchorRamp.value_range r a p).1)

theorem integral_le (r : ℝ) (μ : X→ℝ) (hμ : ∀ p,0 ≤ μ p) (C : Finset X) (a : X) :
    integral r μ C a ≤ ∑ p∈C,μ p :=
  sum_le_sum (fun p _=>mul_le_of_le_one_right (hμ p) (AnchorRamp.value_range r a p).2)

theorem regroup [Fintype X] (r : ℝ) (μ : X→ℝ) (c : H→ℝ) (a : H→X) (key : X→H⊕T) :
    (∑ l : H,c l*integral r μ (univ.filter (fun p=>key p=Sum.inl l)) (a l))=
      ∑ p,μ p*AnchorScalar.value r c a (key p) p := by
  simp only [integral,sum_filter,mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  cases he : key p with
  | inr b => simp only [Sum.inr_ne_inl,ite_false,sum_const_zero,AnchorScalar.value,mul_zero]
  | inl l =>
    simp only [Sum.inl.injEq]
    rw [sum_ite_eq,ite_eq_left (mem_univ l)]
    simp only [AnchorScalar.value]
    ring

theorem reference {K : ℝ} (I : KeySizeTracker.Input Ω K) (r b M V C : ℝ)
    (t : ℕ) (ω : Ω) (hr : 0 ≤ r) (hb : 0 ≤ b) (hV : 0 ≤ V) (hVM : V ≤ M)
    (hs : I.size (t+1) ω=1+M) (hbC : b ≤ C*KeySizeTracker.held I t ω) (hC : 0 ≤ C) :
    r*b/KeySizeTracker.held I (t+1) ω*V-r*b/KeySizeTracker.held I t ω*V ≤ 
      r*C*KeySizeTracker.charge I t ω := by
  by_cases he : KeySizeTracker.keep (I.size (t+1) ω) (KeySizeTracker.held I t ω)
  · simp only [KeySizeTracker.held,ite_eq_left he,KeySizeTracker.charge,sub_self,mul_zero,le_refl]
  · have hu : 0<KeySizeTracker.held I t ω := by have := (KeySizeTracker.held_range I t ω).1; linarith
    have hspos : 0<I.size (t+1) ω := by have := (I.range (t+1) ω).1; linarith
    have h := AnchorScalar.reference r b V M (KeySizeTracker.held I t ω) (I.size (t+1) ω) C
      hr hb hV hVM hu hs hspos hbC hC
    simpa only [KeySizeTracker.held,ite_eq_right he,KeySizeTracker.charge] using h

end UniformKServer.AnchorPotential

end


end

end OAI
